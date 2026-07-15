package yamledit

import (
	"bytes"
	"fmt"
	"sort"
	"strconv"
	"strings"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// effectiveIndentAt returns the indentation level where the key effectively starts.
// For normal lines it's just leading spaces.
// For sequence-item lines like "  - key: ..." it returns (leading spaces + 2),
// because the key starts after "- ".
func effectiveIndentAt(original []byte, start int) int {
	i := start
	for i > 0 && original[i-1] != '\n' {
		i--
	}
	end := findLineEnd(original, i)
	if end < 0 {
		return 0
	}
	// findLineEnd returns index of '\n' or len-1
	line := original[i : end+1]
	ind := leadingSpaces(line)
	if ind < len(line) && line[ind] == '-' {
		if ind+1 < len(line) && (line[ind+1] == ' ' || line[ind+1] == '\t') {
			return ind + 2
		}
	}
	return ind
}

func Marshal(doc *yaml.Node) ([]byte, error) {
	st, ok := lookup(doc)
	if !ok {
		// Fallback if somehow not registered
		if err := validateYAMLAliasGraph(doc); err != nil {
			return nil, err
		}
		var buf bytes.Buffer
		enc := yaml.NewEncoder(&buf)
		enc.SetIndent(2)
		if err := enc.Encode(doc); err != nil {
			_ = enc.Close()
			return nil, err
		}
		if err := enc.Close(); err != nil {
			return nil, err
		}
		return buf.Bytes(), nil
	}

	st.mu.RLock()
	if err := validateYAMLAliasGraph(doc); err != nil {
		st.mu.RUnlock()
		return nil, err
	}
	if err := validateOrderedUTF8(st.ordered); err != nil {
		st.mu.RUnlock()
		return nil, err
	}
	if len(st.original) == 0 {
		// Encode the live AST while holding the read lock. Snapshotting is not
		// sufficient for a new document because the encoder traverses doc itself.
		out, err := standardEncode(doc, st.indent)
		st.mu.RUnlock()
		return out, err
	}
	if st.originalTriviaOnly {
		if logicalEqualOrdered(st.origOrdered, st.ordered) {
			out := append([]byte(nil), st.original...)
			st.mu.RUnlock()
			return out, nil
		}
		encoded, err := standardEncode(doc, st.indent)
		if err != nil {
			st.mu.RUnlock()
			return nil, err
		}
		encoded = normalizePatchLineEndings(st.original, encoded)
		out := append([]byte(nil), st.original...)
		nonBOM := bytes.TrimPrefix(out, []byte{0xef, 0xbb, 0xbf})
		if len(nonBOM) > 0 && out[len(out)-1] != '\n' {
			if firstLF := bytes.IndexByte(st.original, '\n'); firstLF > 0 && st.original[firstLF-1] == '\r' {
				out = append(out, '\r')
			}
			out = append(out, '\n')
		}
		out = append(out, encoded...)
		st.mu.RUnlock()
		return validateEditedOutput(out)
	}
	if st.originalRootEmpty {
		// An explicit `{}` root has no stable key-line anchor for surgery. Keep
		// the exact input for a net-zero edit; otherwise encode the live AST while
		// it is protected by the state lock.
		if logicalEqualOrdered(st.origOrdered, st.ordered) {
			out := append([]byte(nil), st.original...)
			st.mu.RUnlock()
			return out, nil
		}
		if st.rootTokenEnd <= st.rootTokenStart || st.rootTokenEnd > len(st.original) {
			st.mu.RUnlock()
			return nil, fmt.Errorf("yamledit: cannot safely replace explicit empty root mapping")
		}
		rootValue := orderedToYAMLNode(cloneMapSlice(st.ordered))
		// Only the original `{}` token is replaced. Keeping the replacement in
		// flow form prevents a preceding root tag or anchor (`!T {}`, `&a {}`)
		// from binding to the first inserted key instead of the root mapping.
		rootValue.Style |= yaml.FlowStyle
		encodedRoot := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{rootValue}}
		replacement, err := standardEncode(encodedRoot, st.indent)
		if err == nil {
			replacement = bytes.TrimSuffix(replacement, []byte("\n"))
		}
		out := make([]byte, 0, len(st.original)-(st.rootTokenEnd-st.rootTokenStart)+len(replacement))
		out = append(out, st.original[:st.rootTokenStart]...)
		out = append(out, replacement...)
		out = append(out, st.original[st.rootTokenEnd:]...)
		st.mu.RUnlock()
		if err != nil {
			return nil, err
		}
		return validateEditedOutput(out)
	}
	ordered := cloneMapSlice(st.ordered) // snapshot
	indent := st.indent
	original := st.original
	mapIdx := cloneMapIndex(st.mapIndex)
	valIdx := cloneValueIndex(st.valueOccByPathKey)
	boundsIdx := cloneBoundsIndex(st.boundsByPathKey) // Clone new index
	unsafePaths := make(map[string]struct{}, len(st.unsafePathKeys))
	for path := range st.unsafePathKeys {
		unsafePaths[path] = struct{}{}
	}
	semanticOpaquePaths := make(map[string]struct{}, len(st.opaquePathKeys))
	for path := range st.opaquePathKeys {
		semanticOpaquePaths[path] = struct{}{}
	}
	opaquePaths := make(map[string]struct{}, len(semanticOpaquePaths))
	for path := range semanticOpaquePaths {
		opaquePaths[path] = struct{}{}
	}
	presentationOpaquePaths := make(map[string]struct{})
	if doc != nil && doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 {
		markLivePresentationOpaquePaths(doc.Content[0], nil, presentationOpaquePaths)
	}
	for path := range presentationOpaquePaths {
		opaquePaths[path] = struct{}{}
	}
	origOrdered := cloneMapSlice(st.origOrdered)
	delSet := make(map[string]struct{}, len(st.toDelete))
	seqIdx := cloneSeqIndex(st.seqIndex)
	for k := range st.toDelete {
		delSet[k] = struct{}{}
	}
	structuralDirty := st.structuralDirty
	rootMappingEmpty := doc != nil && doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 && doc.Content[0].Kind == yaml.MappingNode && len(doc.Content[0].Content) == 0
	st.mu.RUnlock()

	out, okPatch := marshalBySurgery(original, ordered, origOrdered, mapIdx, valIdx, seqIdx, boundsIdx, unsafePaths, semanticOpaquePaths, presentationOpaquePaths, indent, delSet)
	if okPatch && (!structuralDirty || (bytes.Equal(out, original) && logicalEqualOrdered(origOrdered, ordered))) {
		validated, err := validateEditedOutput(out)
		if err != nil {
			return nil, err
		}
		return validated, nil
	}

	if patched, ok := structuralRewrite(original, ordered, origOrdered, boundsIdx, unsafePaths, opaquePaths, indent, delSet, rootMappingEmpty); ok {
		return validateEditedOutput(patched)
	}

	return nil, fmt.Errorf("yamledit: surgical edit unsupported; no safe structural rewrite")
}

func validateEditedOutput(out []byte) ([]byte, error) {
	var doc yaml.Node
	if err := decodeSingleYAMLDocument(out, &doc); err != nil {
		return nil, fmt.Errorf("yamledit: edit would produce invalid YAML: %w", err)
	}
	if doc.Kind != yaml.DocumentNode || len(doc.Content) == 0 || doc.Content[0].Kind != yaml.MappingNode {
		return nil, fmt.Errorf("yamledit: edit would change the document root from a mapping")
	}
	return out, nil
}

// standardEncode performs a standard YAML encoding without surgical editing.
// Used as fallback when original content is empty or surgical editing fails.
func standardEncode(doc *yaml.Node, indent int) ([]byte, error) {
	if indent <= 0 {
		indent = 2
	}
	var buf bytes.Buffer
	enc := yaml.NewEncoder(&buf)
	enc.SetIndent(indent)
	if err := enc.Encode(doc); err != nil {
		return nil, err
	}
	if err := enc.Close(); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// structuralRewrite surgically re-encodes individual key regions using boundsIdx.
func structuralRewrite(original []byte, ordered gyaml.MapSlice, origOrdered gyaml.MapSlice, boundsIdx map[string][]kvBounds, unsafePaths, opaquePaths map[string]struct{}, baseIndent int, delSet map[string]struct{}, rootMappingEmpty bool) ([]byte, bool) {
	if rootMappingEmpty && len(ordered) == 0 && len(origOrdered) > 0 {
		for pk := range unsafePaths {
			if parts, ok := splitJoinedPath(pk); ok && len(parts) == 1 {
				return nil, false
			}
		}
		// Keep the document root a mapping when its last member is deleted.
		// Replace just the span occupied by top-level entries so header/footer
		// comments and document markers remain untouched.
		start, end := len(original), -1
		for pk, bounds := range boundsIdx {
			parts, ok := splitJoinedPath(pk)
			if !ok || len(parts) != 1 {
				continue
			}
			for _, bound := range bounds {
				if bound.start < start {
					start = bound.start
				}
				if bound.end > end {
					end = bound.end
				}
			}
		}
		if start >= 0 && start <= end && end <= len(original) {
			replacement := []byte("{}")
			if end > start && original[end-1] == '\n' {
				replacement = append(replacement, '\n')
			}
			out := make([]byte, 0, len(original)-(end-start)+len(replacement))
			out = append(out, original[:start]...)
			out = append(out, replacement...)
			out = append(out, original[end:]...)
			return out, true
		}
	}

	var patches []patch
	patched := map[string]struct{}{}
	changed := collectChangedKeysDeep(origOrdered, ordered, nil)
	findSafeContainerAncestor := func(pk string) (string, bool) {
		parts, ok := splitJoinedPath(pk)
		if !ok {
			return "", false
		}
		for i := len(parts) - 1; i >= 1; i-- {
			ancestor := joinPath(parts[:i])
			_, opaque := opaquePaths[ancestor]
			if _, unsafe := unsafePaths[ancestor]; unsafe || opaque || len(boundsIdx[ancestor]) == 0 {
				continue
			}
			parent, key := parts[:i-1], parts[i-1]
			value, exists := orderedValueAt(ordered, parent, key)
			if !exists {
				continue
			}
			switch value.(type) {
			case gyaml.MapSlice, []interface{}:
				return ancestor, true
			}
		}
		return "", false
	}
	changedSeen := make(map[string]struct{}, len(changed))
	for _, pk := range changed {
		changedSeen[pk] = struct{}{}
	}
	promoteUnsafe := func(pk string) {
		if _, unsafe := unsafePaths[pk]; !unsafe {
			return
		}
		if ancestor, ok := findSafeContainerAncestor(pk); ok {
			if _, exists := changedSeen[ancestor]; !exists {
				changed = append(changed, ancestor)
				changedSeen[ancestor] = struct{}{}
			}
		}
	}
	for _, pk := range append([]string(nil), changed...) {
		promoteUnsafe(pk)
	}
	for _, pk := range append([]string(nil), changed...) {
		if len(boundsIdx[pk]) != 0 {
			continue
		}
		if ancestor, ok := findSafeContainerAncestor(pk); ok {
			if _, exists := changedSeen[ancestor]; !exists {
				changed = append(changed, ancestor)
				changedSeen[ancestor] = struct{}{}
			}
		}
	}
	for pk := range delSet {
		promoteUnsafe(pk)
	}
	changedSet := make(map[string]struct{}, len(changed))
	for _, pk := range changed {
		changedSet[pk] = struct{}{}
	}
	hasChangedSafeAncestor := func(pk string) bool {
		parts, ok := splitJoinedPath(pk)
		if !ok {
			return false
		}
		for i := len(parts) - 1; i >= 1; i-- {
			ancestor := joinPath(parts[:i])
			if _, changed := changedSet[ancestor]; !changed {
				continue
			}
			_, opaque := opaquePaths[ancestor]
			if _, unsafe := unsafePaths[ancestor]; unsafe || opaque || len(boundsIdx[ancestor]) == 0 {
				continue
			}
			return true
		}
		return false
	}

	// Build "parent mapping → last child bounds" index so we can insert new keys.
	// Keyed by joinPath(parentPathSegments).
	parentLast := make(map[string]kvBounds, 128)
	for pk, bl := range boundsIdx {
		if len(bl) == 0 {
			continue
		}
		pp, _ := splitPathKey(pk)
		parentKey := joinPath(pp)
		b := bl[len(bl)-1] // last occurrence
		if prev, ok := parentLast[parentKey]; !ok || b.end > prev.end {
			parentLast[parentKey] = b
		}
	}

	// Keys whose entire region we are rewriting (or deleting). Any nested "new key"
	// insertions under these should be skipped, because the rewrite patch already
	// re-encodes the subtree.
	rewritten := make(map[string]struct{}, 64)

	hasRewrittenAncestor := func(pk string) bool {
		segs, ok := splitJoinedPath(pk)
		if !ok {
			return false
		}
		// walk ancestors: a/b/c -> a/b, a
		for i := len(segs) - 1; i >= 1; i-- {
			anc := joinPath(segs[:i])
			if _, ok := rewritten[anc]; ok {
				return true
			}
		}
		return false
	}
	// Deletions: remove key ranges for explicit deletions.
	for pk := range delSet {
		if _, unsafe := unsafePaths[pk]; unsafe {
			if hasChangedSafeAncestor(pk) {
				continue
			}
			return nil, false
		}
		bounds := boundsIdx[pk]
		if len(bounds) == 0 {
			continue
		}
		for _, b := range bounds {
			patches = append(patches, patch{start: b.start, end: b.end, data: []byte{}})
		}
		patched[pk] = struct{}{}
		rewritten[pk] = struct{}{}
	}

	// Structural fallback must honor last-wins duplicate semantics too.
	// Keep only widest ranges so a duplicate parent removal subsumes any
	// duplicate children inside the same block without overlapping patches.
	var duplicateRanges []kvBounds
	for pk, bounds := range boundsIdx {
		if _, unsafe := unsafePaths[pk]; unsafe {
			continue
		}
		if _, deleting := delSet[pk]; deleting || len(bounds) <= 1 {
			continue
		}
		duplicateRanges = append(duplicateRanges, bounds[:len(bounds)-1]...)
	}
	sort.Slice(duplicateRanges, func(i, j int) bool {
		if duplicateRanges[i].start == duplicateRanges[j].start {
			return duplicateRanges[i].end > duplicateRanges[j].end
		}
		return duplicateRanges[i].start < duplicateRanges[j].start
	})
	for _, candidate := range duplicateRanges {
		contained := false
		for _, existing := range patches {
			if len(existing.data) == 0 && existing.start <= candidate.start && existing.end >= candidate.end {
				contained = true
				break
			}
		}
		if !contained {
			patches = append(patches, patch{start: candidate.start, end: candidate.end})
		}
	}

	// Collect insertion candidates (keys that changed but have NO bounds => new keys).
	var insertCands []string
	insertSet := make(map[string]struct{}, 32)

	for _, pk := range changed {
		if _, skip := patched[pk]; skip {
			continue
		}
		if _, unsafe := unsafePaths[pk]; unsafe {
			if hasRewrittenAncestor(pk) || hasChangedSafeAncestor(pk) {
				continue
			}
			return nil, false
		}
		bounds := boundsIdx[pk]
		if len(bounds) == 0 {
			// Candidate for insertion – but only if not already covered by
			// a rewrite patch of an ancestor.
			if hasRewrittenAncestor(pk) {
				continue
			}
			insertCands = append(insertCands, pk)
			insertSet[pk] = struct{}{}
			continue
		}

		path, key := splitPathKey(pk)
		val, ok := orderedValueAt(ordered, path, key)
		if !ok {
			// A complex add/replace can remove members without going through
			// DeleteKey. Remove every original occurrence so stale or duplicate
			// values cannot survive a successful replacement.
			for _, b := range bounds {
				patches = append(patches, patch{start: b.start, end: b.end, data: []byte{}})
			}
			rewritten[pk] = struct{}{}
			continue
		}
		if _, opaque := opaquePaths[pk]; opaque {
			return nil, false
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
			rewritten[pk] = struct{}{}
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
		rewritten[pk] = struct{}{}
	}

	// Reduce insertion candidates: if an ancestor is also new, only insert the top-most one.
	var inserts []string
	for _, pk := range insertCands {
		segs, ok := splitJoinedPath(pk)
		if !ok {
			return nil, false
		}
		skip := false
		for i := len(segs) - 1; i >= 1; i-- {
			anc := joinPath(segs[:i])
			if _, ok := insertSet[anc]; ok {
				skip = true
				break
			}
		}
		if skip {
			continue
		}
		// Also skip if an ancestor rewrite exists (extra safety; ancestors may have been
		// marked rewritten after we collected candidates).
		if hasRewrittenAncestor(pk) {
			continue
		}
		inserts = append(inserts, pk)
	}

	// Emit insertion patches (start==end).
	seenInsertPos := map[int]bool{}
	for _, pk := range inserts {
		parentPath, key := splitPathKey(pk)
		val, ok := orderedValueAt(ordered, parentPath, key)
		if !ok {
			continue
		}

		parentKey := joinPath(parentPath)
		anchor, okAnchor := parentLast[parentKey]
		if !okAnchor {
			// No stable anchor inside this parent mapping → cannot safely insert bytes.
			return nil, false
		}

		insertPos := anchor.end
		if insertPos < 0 || insertPos > len(original) {
			return nil, false
		}
		indentSpaces := effectiveIndentAt(original, anchor.start)

		var sb strings.Builder
		// Only the FIRST insertion at a given position needs to ensure a leading newline.
		if !seenInsertPos[insertPos] {
			if insertPos > 0 && insertPos <= len(original) && original[insertPos-1] != '\n' {
				sb.WriteString("\n")
			}
			seenInsertPos[insertPos] = true
		}

		if !renderInsertedKeyValue(&sb, key, val, indentSpaces, baseIndent) {
			return nil, false
		}
		patches = append(patches, patch{start: insertPos, end: insertPos, data: []byte(sb.String())})
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
		buf.Write(normalizePatchLineEndings(original, p.data))
		cursor = p.end
	}
	if cursor < len(original) {
		buf.Write(original[cursor:])
	}
	return buf.Bytes(), true
}

func splitPathKey(pk string) ([]string, string) {
	parts, ok := splitJoinedPath(pk)
	if !ok || len(parts) == 0 {
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
		switch m := cur.(type) {
		case []interface{}:
			idx, ok := parseIdx(seg)
			if !ok || idx < 0 || idx >= len(m) {
				return nil, false
			}
			cur = m[idx]
		case gyaml.MapSlice:
			found := false
			for i := len(m) - 1; i >= 0; i-- {
				if keyEquals(m[i].Key, seg) {
					cur = m[i].Value
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
		for i := len(m) - 1; i >= 0; i-- {
			if keyEquals(m[i].Key, key) {
				return m[i].Value, true
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
	valueNode := orderedToYAMLNode(val)
	valueNode.Anchor = b.anchor
	if b.collectionTag != "" && (valueNode.Kind == yaml.MappingNode || valueNode.Kind == yaml.SequenceNode) {
		valueNode.Tag = b.collectionTag
	}
	root.Content = append(root.Content,
		&yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key},
		valueNode,
	)
	doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{root}}
	lines, ok := encodeNodeLines(doc, baseIndent)
	if !ok {
		return "", false
	}
	indentSpaces := currentIndent(original, b.start)
	prefix := strings.Repeat(" ", indentSpaces)
	inlineSequenceKey := false
	lineEnd := findLineEnd(original, b.start)
	if lineEnd >= b.start && b.start < len(original) {
		line := original[b.start:min(lineEnd+1, len(original))]
		first := leadingSpaces(line)
		inlineSequenceKey = first+1 < len(line) && line[first] == '-' && (line[first+1] == ' ' || line[first+1] == '\t')
	}
	comment := inlineComment(original, b.start)

	for i := range lines {
		linePrefix := prefix
		if inlineSequenceKey {
			if i == 0 {
				linePrefix += "- "
			} else {
				linePrefix = strings.Repeat(" ", indentSpaces+2)
			}
		}
		if i == 0 && comment != "" {
			lines[i] = linePrefix + lines[i] + " " + comment
		} else {
			lines[i] = linePrefix + lines[i]
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
	if idx := yamlCommentStart(line); idx >= 0 {
		return strings.TrimSpace(string(line[idx:]))
	}
	return ""
}

func yamlCommentStart(line []byte) int {
	inSingle := false
	inDouble := false
	escaped := false
	for i := 0; i < len(line); i++ {
		c := line[i]
		if inDouble {
			if escaped {
				escaped = false
				continue
			}
			if c == '\\' {
				escaped = true
			} else if c == '"' {
				inDouble = false
			}
			continue
		}
		if inSingle {
			if c == '\'' {
				if i+1 < len(line) && line[i+1] == '\'' {
					i++
					continue
				}
				inSingle = false
			}
			continue
		}
		switch c {
		case '"':
			inDouble = true
		case '\'':
			inSingle = true
		case '#':
			if i == 0 || line[i-1] == ' ' || line[i-1] == '\t' {
				return i
			}
		}
	}
	return -1
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
	mapLikeLen := func(v interface{}) int {
		switch m := v.(type) {
		case gyaml.MapSlice:
			return len(m)
		case map[string]interface{}:
			return len(m)
		case map[interface{}]interface{}:
			return len(m)
		default:
			return -1
		}
	}
	mapLikeHasRemoval := func(original, current interface{}) bool {
		originalMap, originalOK := original.(gyaml.MapSlice)
		currentMap, currentOK := current.(gyaml.MapSlice)
		if !originalOK || !currentOK {
			return false
		}
		seen := make(map[string]struct{})
		for _, item := range originalMap {
			key, ok := item.Key.(string)
			if !ok {
				continue
			}
			if _, duplicate := seen[key]; duplicate {
				continue
			}
			seen[key] = struct{}{}
			if _, exists := findLast(currentMap, key); !exists {
				return true
			}
		}
		return false
	}
	mapLikeHasAddition := func(original, current interface{}) bool {
		originalMap, originalOK := original.(gyaml.MapSlice)
		currentMap, currentOK := current.(gyaml.MapSlice)
		if !originalOK || !currentOK {
			return false
		}
		seen := make(map[string]struct{})
		for _, item := range currentMap {
			key, ok := item.Key.(string)
			if !ok {
				continue
			}
			if _, duplicate := seen[key]; duplicate {
				continue
			}
			seen[key] = struct{}{}
			if _, exists := findLast(originalMap, key); !exists {
				return true
			}
		}
		return false
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
		for itemIndex, it := range c {
			k, ok := it.Key.(string)
			if !ok {
				continue
			}
			shadowed := false
			for later := itemIndex + 1; later < len(c); later++ {
				if keyEquals(c[later].Key, k) {
					shadowed = true
					break
				}
			}
			if shadowed {
				continue
			}
			ov, okOrig := findLast(o, k)
			cv := it.Value

			// Recurse into nested mappings.
			if subCur, ok := cv.(gyaml.MapSlice); ok {
				// Preserve the old behavior for map shape transitions.
				if !okOrig || !logicalEqual(toPlain(ov), toPlain(cv)) {
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
						oldMapLen, newMapLen := mapLikeLen(oel), mapLikeLen(cel)
						if (oldMapLen == 0) != (newMapLen == 0) || mapLikeHasRemoval(oel, cel) || mapLikeHasAddition(oel, cel) {
							needWholeSeqRewrite = true
							break
						}
						p2 := appendSeg(appendSeg(path, k), indexSeg(i))
						out = append(out, collectChangedKeysDeep(oel, cel, p2)...)
						continue
					}
					if !logicalEqual(toPlain(oel), toPlain(cel)) {
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
			if !okOrig || !logicalEqual(toPlain(ov), toPlain(cv)) {
				out = append(out, makePathKey(path, k))
			}
		}
		// Also report keys that existed in the original mapping but are absent
		// now. Walking only the current mapping made object replacement retain
		// omitted members indefinitely.
		seenMissing := make(map[string]struct{})
		for _, it := range o {
			k, ok := it.Key.(string)
			if !ok {
				continue
			}
			if _, duplicate := seenMissing[k]; duplicate {
				continue
			}
			if _, exists := findLast(c, k); exists {
				continue
			}
			seenMissing[k] = struct{}{}
			out = append(out, makePathKey(path, k))
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
	comment := inlineComment(original, b.start)

	var sb strings.Builder
	sb.WriteString(strings.Repeat(" ", indentSpaces))
	sb.WriteString(renderMappingKey(key))
	if len(arr) == 0 {
		sb.WriteString(":")
		if b.collectionTag != "" {
			sb.WriteString(" ")
			sb.WriteString(renderYAMLTagProperty(b.collectionTag))
		}
		if b.anchor != "" {
			sb.WriteString(" &")
			sb.WriteString(b.anchor)
		}
		sb.WriteString(" []")
		if comment != "" {
			sb.WriteString(" ")
			sb.WriteString(comment)
		}
		if b.end > b.start && b.end <= len(original) && original[b.end-1] == '\n' {
			sb.WriteString("\n")
		}
		return sb.String(), true
	}
	sb.WriteString(":")
	if b.collectionTag != "" {
		sb.WriteString(" ")
		sb.WriteString(renderYAMLTagProperty(b.collectionTag))
	}
	if b.anchor != "" {
		sb.WriteString(" &")
		sb.WriteString(b.anchor)
	}
	if comment != "" {
		sb.WriteString(" ")
		sb.WriteString(comment)
	}
	sb.WriteString("\n")

	// dashIndent is where sequence items start under this key.
	dashIndent := indentSpaces + baseIndent
	for _, el := range arr {
		if !renderYAMLSequenceElement(&sb, el, dashIndent, baseIndent) {
			return "", false
		}
	}
	// Trim trailing newline if original region had none.
	if b.end <= len(original) && b.end > b.start && original[b.end-1] != '\n' {
		out := sb.String()
		out = strings.TrimSuffix(out, "\n")
		return out, true
	}
	return sb.String(), true
}

func renderYAMLTagProperty(tag string) string {
	if strings.HasPrefix(tag, "!") {
		return tag
	}
	return "!<" + tag + ">"
}

func renderScalarLine(v interface{}) string {
	if rendered, ok := renderScalarToken(v); ok {
		return rendered
	}
	b, err := yaml.Marshal(v)
	if err != nil {
		return fmt.Sprint(v)
	}
	return strings.TrimSpace(string(b))
}
