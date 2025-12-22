package yamledit

import (
	"bytes"
	"fmt"
	"reflect"
	"sort"
	"strconv"
	"strings"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

func Marshal(doc *yaml.Node) ([]byte, error) {
	st, ok := lookup(doc)
	if !ok {
		// Fallback if somehow not registered
		var buf bytes.Buffer
		enc := yaml.NewEncoder(&buf)
		enc.SetIndent(2)
		_ = enc.Encode(doc)
		_ = enc.Close()
		return buf.Bytes(), nil
	}

	st.mu.RLock()
	ordered := cloneMapSlice(st.ordered) // snapshot
	indent := st.indent
	original := st.original
	mapIdx := cloneMapIndex(st.mapIndex)
	valIdx := cloneValueIndex(st.valueOccByPathKey)
	boundsIdx := cloneBoundsIndex(st.boundsByPathKey) // Clone new index
	origOrdered := cloneMapSlice(st.origOrdered)
	delSet := make(map[string]struct{}, len(st.toDelete))
	seqIdx := cloneSeqIndex(st.seqIndex)
	for k := range st.toDelete {
		delSet[k] = struct{}{}
	}
	arraysDirty := st.arraysDirty
	structuralDirty := st.structuralDirty
	st.mu.RUnlock()

	out, okPatch := marshalBySurgery(original, ordered, origOrdered, mapIdx, valIdx, seqIdx, boundsIdx, indent, delSet)
	if okPatch && !structuralDirty {
		if arraysDirty {
			if s, ok := lookup(doc); ok {
				s.mu.Lock()
				s.arraysDirty = false
				s.mu.Unlock()
			}
		}
		return out, nil
	}

	if patched, ok := structuralRewrite(original, ordered, origOrdered, boundsIdx, indent, delSet); ok {
		return patched, nil
	}

	return nil, fmt.Errorf("yamledit: surgical edit unsupported; no safe structural rewrite")
}

// structuralRewrite surgically re-encodes individual key regions using boundsIdx.
func structuralRewrite(original []byte, ordered gyaml.MapSlice, origOrdered gyaml.MapSlice, boundsIdx map[string][]kvBounds, baseIndent int, delSet map[string]struct{}) ([]byte, bool) {
	var patches []patch
	patched := map[string]struct{}{}

	// Deletions: remove key ranges for explicit deletions.
	for pk := range delSet {
		bounds := boundsIdx[pk]
		if len(bounds) == 0 {
			continue
		}
		b := bounds[len(bounds)-1]
		patches = append(patches, patch{start: b.start, end: b.end, data: []byte{}})
		patched[pk] = struct{}{}
	}

	changed := collectChangedKeysDeep(origOrdered, ordered, nil)
	for _, pk := range changed {
		if _, skip := patched[pk]; skip {
			continue
		}
		bounds := boundsIdx[pk]
		if len(bounds) == 0 {
			continue
		}
		path, key := splitPathKey(pk)
		val, ok := orderedValueAt(ordered, path, key)
		if !ok {
			continue
		}
		b := bounds[len(bounds)-1]
		if isSequence(val) {
			seqText, okSeq := renderSequenceValue(original, key, val, b, baseIndent)
			if !okSeq {
				return nil, false
			}
			if bytes.Equal(original[b.start:b.end], []byte(seqText)) {
				continue
			}
			patches = append(patches, patch{start: b.start, end: b.end, data: []byte(seqText)})
			continue
		}

		txt, ok := renderKeyValue(original, key, val, b, baseIndent)
		if !ok {
			continue
		}
		if bytes.Equal(original[b.start:b.end], []byte(txt)) {
			continue
		}
		patches = append(patches, patch{start: b.start, end: b.end, data: []byte(txt)})
	}

	if len(patches) == 0 {
		return nil, false
	}

	sort.SliceStable(patches, func(i, j int) bool {
		if patches[i].start == patches[j].start {
			return patches[i].end < patches[j].end
		}
		return patches[i].start < patches[j].start
	})

	var filtered []patch
	for _, p := range patches {
		if len(filtered) == 0 {
			filtered = append(filtered, p)
			continue
		}
		last := &filtered[len(filtered)-1]
		if p.start < last.end {
			// Overlap: keep earlier (outer) patch, skip this one.
			continue
		}
		filtered = append(filtered, p)
	}

	var buf bytes.Buffer
	cursor := 0
	for _, p := range filtered {
		if p.start < cursor || p.end < p.start || p.end > len(original) {
			return nil, false
		}
		buf.Write(original[cursor:p.start])
		buf.Write(p.data)
		cursor = p.end
	}
	if cursor < len(original) {
		buf.Write(original[cursor:])
	}
	return buf.Bytes(), true
}

func splitPathKey(pk string) ([]string, string) {
	parts := strings.Split(pk, pathSep)
	if len(parts) == 0 {
		return nil, ""
	}
	return parts[:len(parts)-1], parts[len(parts)-1]
}

func orderedValueAt(ms gyaml.MapSlice, path []string, key string) (interface{}, bool) {
	parseIdx := func(seg string) (int, bool) {
		if len(seg) > 2 && seg[0] == '[' && seg[len(seg)-1] == ']' {
			i, err := strconv.Atoi(seg[1 : len(seg)-1])
			if err == nil {
				return i, true
			}
		}
		return 0, false
	}

	var cur interface{} = ms
	for _, seg := range path {
		if idx, ok := parseIdx(seg); ok {
			arr, okArr := cur.([]interface{})
			if !okArr || idx < 0 || idx >= len(arr) {
				return nil, false
			}
			cur = arr[idx]
			continue
		}

		switch m := cur.(type) {
		case gyaml.MapSlice:
			found := false
			for _, it := range m {
				if keyEquals(it.Key, seg) {
					cur = it.Value
					found = true
					break
				}
			}
			if !found {
				return nil, false
			}
		case map[string]interface{}:
			v, ok := m[seg]
			if !ok {
				return nil, false
			}
			cur = v
		default:
			return nil, false
		}
	}

	switch m := cur.(type) {
	case gyaml.MapSlice:
		for _, it := range m {
			if keyEquals(it.Key, key) {
				return it.Value, true
			}
		}
		return nil, false
	case map[string]interface{}:
		v, ok := m[key]
		return v, ok
	default:
		return nil, false
	}
}

func renderKeyValue(original []byte, key string, val interface{}, b kvBounds, baseIndent int) (string, bool) {
	// IMPORTANT: do NOT convert to map[string]interface{} (it loses key order).
	// Build a yaml.Node mapping and encode that (preserves gyaml.MapSlice order).
	root := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
	root.Content = append(root.Content,
		&yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key},
		orderedToYAMLNode(val),
	)
	doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{root}}
	lines, ok := encodeNodeLines(doc, baseIndent)
	if !ok {
		return "", false
	}
	indentSpaces := currentIndent(original, b.start)
	prefix := strings.Repeat(" ", indentSpaces)
	comment := inlineComment(original, b.start)

	for i := range lines {
		if i == 0 && comment != "" {
			lines[i] = prefix + lines[i] + " " + comment
		} else {
			lines[i] = prefix + lines[i]
		}
	}
	out := strings.Join(lines, "\n")
	if b.end > b.start && b.end <= len(original) && original[b.end-1] == '\n' {
		out += "\n"
	}
	return out, true
}

func currentIndent(original []byte, start int) int {
	i := start
	for i > 0 && original[i-1] != '\n' {
		i--
	}
	end := findLineEnd(original, i)
	if end >= len(original) {
		end = len(original)
	}
	return leadingSpaces(original[i:end])
}

func inlineComment(original []byte, start int) string {
	i := start
	for i > 0 && original[i-1] != '\n' {
		i--
	}
	end := findLineEnd(original, i)
	if end >= len(original) {
		end = len(original) - 1
	}
	line := original[i : end+1]
	if idx := bytes.IndexByte(line, '#'); idx >= 0 {
		return strings.TrimSpace(string(line[idx:]))
	}
	return ""
}

func collectChangedKeysDeep(orig interface{}, cur interface{}, path []string) []string {
	isMapLike := func(v interface{}) bool {
		switch v.(type) {
		case gyaml.MapSlice, map[string]interface{}, map[interface{}]interface{}:
			return true
		default:
			return false
		}
	}
	appendSeg := func(base []string, seg string) []string {
		out := append([]string(nil), base...)
		return append(out, seg)
	}

	switch c := cur.(type) {
	case gyaml.MapSlice:
		var o gyaml.MapSlice
		if om, ok := orig.(gyaml.MapSlice); ok {
			o = om
		}
		var out []string
		for _, it := range c {
			k, ok := it.Key.(string)
			if !ok {
				continue
			}
			ov, okOrig := findLast(o, k)
			cv := it.Value

			// Recurse into nested mappings.
			if subCur, ok := cv.(gyaml.MapSlice); ok {
				// Preserve the old behavior for map shape transitions.
				if !okOrig || !reflect.DeepEqual(toPlain(ov), toPlain(cv)) {
					if ovMs, okMs := ov.(gyaml.MapSlice); !okMs || len(subCur) == 0 || len(ovMs) == 0 {
						out = append(out, makePathKey(path, k))
					}
				}
				out = append(out, collectChangedKeysDeep(ov, subCur, appendSeg(path, k))...)
				continue
			}

			// Recurse into sequences when possible (arrays of maps).
			if curArr, ok := cv.([]interface{}); ok {
				origArr, okArr := ov.([]interface{})
				if !okOrig || !okArr {
					out = append(out, makePathKey(path, k))
					continue
				}
				// Length changes => rewrite the whole sequence key.
				if len(curArr) != len(origArr) {
					out = append(out, makePathKey(path, k))
					continue
				}

				// Same length: if elements are maps, diff inside them by index.
				// If we hit scalar/mixed/unknown changes, fall back to rewriting the whole sequence key.
				needWholeSeqRewrite := false
				for i := 0; i < len(curArr); i++ {
					oel := origArr[i]
					cel := curArr[i]
					if isMapLike(oel) && isMapLike(cel) {
						p2 := appendSeg(appendSeg(path, k), indexSeg(i))
						out = append(out, collectChangedKeysDeep(oel, cel, p2)...)
						continue
					}
					if !reflect.DeepEqual(toPlain(oel), toPlain(cel)) {
						needWholeSeqRewrite = true
						break
					}
				}
				if needWholeSeqRewrite {
					out = append(out, makePathKey(path, k))
				}
				continue
			}

			// Scalars / non-container values.
			if !okOrig || !reflect.DeepEqual(toPlain(ov), toPlain(cv)) {
				out = append(out, makePathKey(path, k))
			}
		}
		return out
	default:
		return nil
	}
}

func findLast(ms gyaml.MapSlice, key string) (interface{}, bool) {
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, key) {
			return ms[i].Value, true
		}
	}
	return nil, false
}

func isSequence(v interface{}) bool {
	switch v.(type) {
	case []interface{}:
		return true
	default:
		return false
	}
}

func renderSequenceValue(original []byte, key string, val interface{}, b kvBounds, baseIndent int) (string, bool) {
	arr, ok := val.([]interface{})
	if !ok {
		return "", false
	}
	indentSpaces := currentIndent(original, b.start)

	var sb strings.Builder
	sb.WriteString(strings.Repeat(" ", indentSpaces))
	sb.WriteString(key)
	if len(arr) == 0 {
		sb.WriteString(": []")
		if b.end > b.start && b.end <= len(original) && original[b.end-1] == '\n' {
			sb.WriteString("\n")
		}
		return sb.String(), true
	}
	sb.WriteString(":\n")

	// dashIndent is where "- " starts for items under this key.
	dashIndent := indentSpaces + baseIndent
	// continuationIndent aligns subsequent lines under the first key after "- ".
	continuationIndent := dashIndent + 2

	isMapLike := func(v interface{}) bool {
		switch v.(type) {
		case gyaml.MapSlice, map[string]interface{}, map[interface{}]interface{}:
			return true
		default:
			return false
		}
	}

	encodeAsLines := func(v interface{}) ([]string, bool) {
		// IMPORTANT: do NOT call toPlain(v) here, it destroys gyaml.MapSlice ordering
		// and the yaml encoder will reorder keys (your exact bug).
		n := orderedToYAMLNode(v)
		// yaml encoder prefers DocumentNode; strip '---' if any.
		doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{n}}
		return encodeNodeLines(doc, baseIndent)
	}

	for _, el := range arr {
		// If the element is a mapping, render it as a proper YAML list item
		// instead of going through renderScalarLine (which produces "- key/value" noise).
		if isMapLike(el) {
			lines, ok := encodeAsLines(el)
			if !ok {
				return "", false
			}
			if len(lines) == 0 {
				// empty map -> "- {}"
				sb.WriteString(strings.Repeat(" ", dashIndent))
				sb.WriteString("- {}")
				sb.WriteString("\n")
				continue
			}

			// First line gets the dash.
			sb.WriteString(strings.Repeat(" ", dashIndent))
			sb.WriteString("- ")
			sb.WriteString(lines[0])
			sb.WriteString("\n")

			// Subsequent lines align under the first key (2 spaces after dashIndent).
			for i := 1; i < len(lines); i++ {
				sb.WriteString(strings.Repeat(" ", continuationIndent))
				sb.WriteString(lines[i])
				sb.WriteString("\n")
			}
			continue
		}

		// Scalar item: keep existing behavior.
		line := renderScalarLine(el)
		sb.WriteString(strings.Repeat(" ", dashIndent))
		sb.WriteString("- ")
		sb.WriteString(line)
		sb.WriteString("\n")
	}
	// Trim trailing newline if original region had none.
	if b.end <= len(original) && b.end > b.start && original[b.end-1] != '\n' {
		out := sb.String()
		out = strings.TrimSuffix(out, "\n")
		return out, true
	}
	return sb.String(), true
}

func renderScalarLine(v interface{}) string {
	switch t := v.(type) {
	case string:
		if isSafeBareString(t) {
			return t
		}
		return quoteNewStringToken(t)
	case int:
		return fmt.Sprintf("%d", t)
	case float64:
		return strconv.FormatFloat(t, 'g', -1, 64)
	case bool:
		if t {
			return "true"
		}
		return "false"
	default:
		b, err := yaml.Marshal(v)
		if err != nil {
			return fmt.Sprint(v)
		}
		return strings.TrimSpace(string(b))
	}
}
