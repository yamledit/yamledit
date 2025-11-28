package yamledit

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"strings"
	"sync"

	jsonpatch "github.com/evanphx/json-patch/v5"
	"gopkg.in/yaml.v3"
)

// docMeta holds formatting hints captured at parse time.
type docMeta struct {
	indent       int
	finalNewline bool
	// raw preserves the original document bytes so we can apply small
	// whitespace touch-ups (e.g. indentless sequences) after encoding.
	raw           []byte
	indentless    []indentlessInfo
	commentSpaces map[string]int
	blockScalars  map[*yaml.Node]blockInfo
}

type blockInfo struct {
	header string
	body   string
	indent int
}

type indentlessInfo struct {
	key    string
	indent int
}

var (
	metaMu    sync.RWMutex
	metaByDoc = map[*yaml.Node]docMeta{}
)

// Parse reads YAML data into a yaml.Node document while recording formatting hints.
func Parse(data []byte) (*yaml.Node, error) {
	var doc yaml.Node
	if len(bytes.TrimSpace(data)) == 0 {
		// Create empty mapping document.
		doc.Kind = yaml.DocumentNode
		doc.Content = []*yaml.Node{{Kind: yaml.MappingNode, Tag: "!!map"}}
		storeMeta(&doc, data)
		return &doc, nil
	}

	dec := yaml.NewDecoder(bytes.NewReader(data))
	dec.KnownFields(false)
	if err := dec.Decode(&doc); err != nil {
		return nil, err
	}
	if doc.Kind != yaml.DocumentNode || len(doc.Content) == 0 || doc.Content[0].Kind != yaml.MappingNode {
		return nil, errors.New("top-level YAML must be a mapping")
	}
	storeMeta(&doc, data)
	return &doc, nil
}

func storeMeta(doc *yaml.Node, data []byte) {
	indent := detectIndent(data)
	finalNL := bytes.HasSuffix(data, []byte("\n"))
	indentless := detectIndentlessSequences(data)
	commentSpaces := captureCommentSpacing(data)
	blockScalars := captureBlockScalars(doc, data)
	metaMu.Lock()
	metaByDoc[doc] = docMeta{indent: indent, finalNewline: finalNL, raw: append([]byte(nil), data...), indentless: indentless, commentSpaces: commentSpaces, blockScalars: blockScalars}
	metaMu.Unlock()
}

// EnsurePath navigates or creates nested mapping nodes for the provided keys.
// The input node may be a document or a mapping node.
func EnsurePath(n *yaml.Node, path ...string) *yaml.Node {
	if n == nil {
		return nil
	}
	// If document node, move to its content.
	if n.Kind == yaml.DocumentNode {
		if len(n.Content) == 0 {
			n.Content = []*yaml.Node{{Kind: yaml.MappingNode, Tag: "!!map"}}
		}
		n = n.Content[0]
	}
	current := n
	for _, key := range path {
		if current.Kind == yaml.ScalarNode {
			// convert scalar to mapping
			current.Kind = yaml.MappingNode
			current.Tag = "!!map"
			current.Value = ""
			current.Content = []*yaml.Node{}
		}
		if current.Kind != yaml.MappingNode {
			// unsupported shape
			return nil
		}
		// find key
		var val *yaml.Node
		var keyNode *yaml.Node
		for i := 0; i < len(current.Content); i += 2 {
			k := current.Content[i]
			if k.Value == key {
				val = current.Content[i+1]
				keyNode = k
				break
			}
		}
		if val == nil {
			k := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
			v := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			current.Content = append(current.Content, k, v)
			val = v
		}
		if val.Kind == yaml.ScalarNode {
			// existing scalar should be promoted to mapping so nested paths work
			if keyNode != nil && keyNode.LineComment == "" {
				keyNode.LineComment = val.LineComment
			}
			val.LineComment = ""
			val.Kind = yaml.MappingNode
			val.Tag = "!!map"
			val.Value = ""
			val.Content = []*yaml.Node{}
		}
		current = val
	}
	return current
}

// SetScalarInt sets an integer scalar value under key within mapping node.
func SetScalarInt(m *yaml.Node, key string, v int) {
	setScalarValue(m, key, fmt.Sprintf("%d", v), "!!int", yaml.Style(0))
}

// SetScalarBool sets a boolean scalar value under key within mapping node.
func SetScalarBool(m *yaml.Node, key string, v bool) {
	val := "false"
	if v {
		val = "true"
	}
	setScalarValue(m, key, val, "!!bool", yaml.Style(0))
}

// SetScalarString sets a string scalar value, preserving existing quote style when possible.
func SetScalarString(m *yaml.Node, key, v string) {
	// Check existing node style.
	var style yaml.Style
	if existing := getMapValue(m, key); existing != nil && existing.Kind == yaml.ScalarNode {
		style = existing.Style
	} else {
		// default to double quoted
		style = yaml.DoubleQuotedStyle
	}
	setScalarValue(m, key, v, "!!str", style)
}

func setScalarValue(m *yaml.Node, key, val, tag string, style yaml.Style) {
	if m == nil {
		return
	}
	if m.Kind == yaml.DocumentNode {
		if len(m.Content) == 0 {
			m.Content = []*yaml.Node{{Kind: yaml.MappingNode, Tag: "!!map"}}
		}
		m = m.Content[0]
	}
	if m.Kind != yaml.MappingNode {
		return
	}
	var target *yaml.Node
	for i := 0; i < len(m.Content); i += 2 {
		k := m.Content[i]
		if k.Value == key {
			target = m.Content[i+1]
			break
		}
	}
	if target == nil {
		k := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
		target = &yaml.Node{Kind: yaml.ScalarNode, Tag: tag, Value: val, Style: style}
		m.Content = append(m.Content, k, target)
		return
	}
	target.Kind = yaml.ScalarNode
	target.Tag = tag
	target.Value = val
	if style != yaml.Style(0) {
		target.Style = style
	} else {
		target.Style = 0
	}
}

func getMapValue(m *yaml.Node, key string) *yaml.Node {
	if m == nil {
		return nil
	}
	if m.Kind == yaml.DocumentNode && len(m.Content) > 0 {
		m = m.Content[0]
	}
	if m.Kind != yaml.MappingNode {
		return nil
	}
	for i := 0; i < len(m.Content); i += 2 {
		if m.Content[i].Value == key {
			return m.Content[i+1]
		}
	}
	return nil
}

// DeleteKey removes all instances of the key from the mapping node.
func DeleteKey(m *yaml.Node, key string) {
	if m == nil {
		return
	}
	if m.Kind == yaml.DocumentNode && len(m.Content) > 0 {
		m = m.Content[0]
	}
	if m.Kind != yaml.MappingNode {
		return
	}
	filtered := make([]*yaml.Node, 0, len(m.Content))
	for i := 0; i < len(m.Content); i += 2 {
		k := m.Content[i]
		v := m.Content[i+1]
		if k.Value == key {
			continue
		}
		filtered = append(filtered, k, v)
	}
	m.Content = filtered
}

// Marshal encodes the YAML document preserving indent and final newline when possible.
func Marshal(doc *yaml.Node) ([]byte, error) {
	if doc == nil {
		return nil, errors.New("nil document")
	}
	metaMu.RLock()
	meta := metaByDoc[doc]
	metaMu.RUnlock()
	if meta.indent == 0 {
		meta.indent = 2
	}
	normalizeEmptyMaps(doc)
	ensureEmptyMapsFlow(doc)
	var buf bytes.Buffer
	enc := yaml.NewEncoder(&buf)
	enc.SetIndent(meta.indent)
	err := enc.Encode(doc)
	enc.Close()
	if err != nil {
		return nil, err
	}
	out := buf.Bytes()
	if !meta.finalNewline {
		out = bytes.TrimSuffix(out, []byte("\n"))
	}
	if len(meta.indentless) > 0 {
		out = restoreIndentlessSequences(out, meta.indent, meta.indentless)
	}
	if len(meta.commentSpaces) > 0 {
		out = applyCommentSpacing(out, meta.commentSpaces)
	}
	if len(meta.blockScalars) > 0 {
		out = applyBlockScalarText(out, meta.blockScalars)
	}
	return out, nil
}

// ApplyJSONPatch applies a patch to the provided mapping/document root.
func ApplyJSONPatch(target *yaml.Node, patch jsonpatch.Patch) error {
	return ApplyJSONPatchAtPath(target, patch, nil)
}

// ApplyJSONPatchAtPath applies patch relative to the provided path inside the document.
func ApplyJSONPatchAtPath(doc *yaml.Node, patch jsonpatch.Patch, path []string) error {
	payload, err := json.Marshal(patch)
	if err != nil {
		return err
	}
	return ApplyJSONPatchAtPathBytes(doc, payload, path)
}

// ApplyJSONPatchAtPathBytes decodes raw patch bytes and applies to a given path.
func ApplyJSONPatchAtPathBytes(doc *yaml.Node, payload []byte, path []string) error {
	var ops []patchOp
	if err := json.Unmarshal(payload, &ops); err != nil {
		return err
	}
	target := EnsurePath(doc, path...)
	if target == nil {
		return errors.New("invalid path")
	}
	for _, op := range ops {
		if err := applyOp(target, op); err != nil {
			return err
		}
	}
	return nil
}

// ApplyJSONPatchBytes applies a JSON patch to the document root.
func ApplyJSONPatchBytes(doc *yaml.Node, payload []byte) error {
	return ApplyJSONPatchAtPathBytes(doc, payload, nil)
}

type patchOp struct {
	Op    string          `json:"op"`
	Path  string          `json:"path"`
	Value json.RawMessage `json:"value"`
}

func applyOp(root *yaml.Node, op patchOp) error {
	switch op.Op {
	case "add":
		return applyAdd(root, op.Path, op.Value)
	case "replace":
		return applyReplace(root, op.Path, op.Value)
	case "remove":
		return applyRemove(root, op.Path)
	case "test":
		return applyTest(root, op.Path, op.Value)
	default:
		return fmt.Errorf("unsupported op %s", op.Op)
	}
}

func parsePointer(p string) []string {
	if p == "" || p == "/" {
		return []string{}
	}
	parts := strings.Split(p, "/")
	if parts[0] == "" {
		parts = parts[1:]
	}
	for i, s := range parts {
		s = strings.ReplaceAll(s, "~1", "/")
		s = strings.ReplaceAll(s, "~0", "~")
		parts[i] = s
	}
	return parts
}

func applyAdd(root *yaml.Node, path string, value json.RawMessage) error {
	tokens := parsePointer(path)
	if len(tokens) == 0 {
		// replace whole node
		newNode, err := jsonToYAMLNode(value)
		if err != nil {
			return err
		}
		*root = *newNode
		return nil
	}
	parent, key := navigateParent(root, tokens)
	if parent == nil {
		return errors.New("path not found")
	}
	valNode, err := jsonToYAMLNode(value)
	if err != nil {
		return err
	}
	switch parent.Kind {
	case yaml.MappingNode:
		replaceOrAddMap(parent, key, valNode, true)
	case yaml.SequenceNode:
		idx := parseIndex(key, len(parent.Content))
		if key == "-" || idx >= len(parent.Content) {
			parent.Content = append(parent.Content, valNode)
		} else if idx >= 0 {
			// insert at idx
			parent.Content = append(parent.Content[:idx], append([]*yaml.Node{valNode}, parent.Content[idx:]...)...)
		} else {
			return errors.New("invalid index")
		}
	default:
		return errors.New("invalid parent kind")
	}
	return nil
}

func applyReplace(root *yaml.Node, path string, value json.RawMessage) error {
	tokens := parsePointer(path)
	if len(tokens) == 0 {
		newNode, err := jsonToYAMLNode(value)
		if err != nil {
			return err
		}
		if root.Kind == yaml.SequenceNode && newNode.Kind == yaml.SequenceNode {
			merged := mergeSequences(root, newNode)
			*root = *merged
		} else {
			*root = *newNode
		}
		return nil
	}
	parent, key := navigateParent(root, tokens)
	if parent == nil {
		return errors.New("path not found")
	}
	valNode, err := jsonToYAMLNode(value)
	if err != nil {
		return err
	}
	switch parent.Kind {
	case yaml.MappingNode:
		replaceOrAddMap(parent, key, valNode, false)
	case yaml.SequenceNode:
		idx := parseIndex(key, len(parent.Content))
		if idx >= 0 && idx < len(parent.Content) {
			copyComments(parent.Content[idx], valNode)
			if valNode.Kind == yaml.ScalarNode && parent.Content[idx].Kind == yaml.ScalarNode && parent.Content[idx].Style != yaml.Style(0) {
				valNode.Style = parent.Content[idx].Style
			}
			parent.Content[idx] = valNode
			return nil
		}
		return errors.New("index out of range")
	default:
		return errors.New("invalid parent kind")
	}
	return nil
}

func applyRemove(root *yaml.Node, path string) error {
	tokens := parsePointer(path)
	if len(tokens) == 0 {
		// replace with null
		*root = yaml.Node{Kind: yaml.ScalarNode, Tag: "!!null"}
		return nil
	}
	parent, key := navigateParent(root, tokens)
	if parent == nil {
		return errors.New("path not found")
	}
	switch parent.Kind {
	case yaml.MappingNode:
		removeMapKey(parent, key)
	case yaml.SequenceNode:
		idx := parseIndex(key, len(parent.Content))
		if idx >= 0 && idx < len(parent.Content) {
			parent.Content = append(parent.Content[:idx], parent.Content[idx+1:]...)
		}
	default:
		return errors.New("invalid parent kind")
	}
	return nil
}

func applyTest(root *yaml.Node, path string, value json.RawMessage) error {
	target := getNodeAt(root, parsePointer(path))
	if target == nil {
		return errors.New("path not found")
	}
	valNode, err := jsonToYAMLNode(value)
	if err != nil {
		return err
	}
	if !nodesEqual(target, valNode) {
		return errors.New("test op failed")
	}
	return nil
}

func nodesEqual(a, b *yaml.Node) bool {
	if a.Kind != b.Kind || a.Tag != b.Tag || a.Value != b.Value || len(a.Content) != len(b.Content) {
		return false
	}
	for i := range a.Content {
		if !nodesEqual(a.Content[i], b.Content[i]) {
			return false
		}
	}
	return true
}

// copyComments copies inline and block comments from src to dst when present.
func copyComments(src, dst *yaml.Node) {
	if src == nil || dst == nil {
		return
	}
	if src.HeadComment != "" {
		dst.HeadComment = src.HeadComment
	}
	if src.LineComment != "" {
		dst.LineComment = src.LineComment
	}
	if src.FootComment != "" {
		dst.FootComment = src.FootComment
	}
}

// mergeSequences attempts to preserve ordering, styles, and comments from the existing
// sequence while applying the new content.
func mergeSequences(existing, updated *yaml.Node) *yaml.Node {
	if existing == nil || updated == nil || existing.Kind != yaml.SequenceNode || updated.Kind != yaml.SequenceNode {
		return updated
	}
	merged := &yaml.Node{Kind: yaml.SequenceNode, Tag: updated.Tag, Style: updated.Style, Anchor: updated.Anchor, HeadComment: existing.HeadComment, LineComment: existing.LineComment, FootComment: existing.FootComment}

	nameIndex := map[string]*yaml.Node{}
	for _, item := range existing.Content {
		if name := mappingName(item); name != "" {
			nameIndex[name] = item
		}
	}

	for i, item := range updated.Content {
		var out *yaml.Node
		if name := mappingName(item); name != "" {
			if orig, ok := nameIndex[name]; ok && orig.Kind == yaml.MappingNode {
				// Update existing mapping in-place to preserve key order and comments.
				mergedMap := cloneNode(orig)
				mergeMappingPreserveOrder(mergedMap, item)
				out = mergedMap
			}
		}
		if out == nil && i < len(existing.Content) && existing.Content[i].Kind == item.Kind {
			// Reuse positional sibling for scalars to keep inline comments/styles.
			if item.Kind == yaml.ScalarNode {
				cloned := cloneNode(existing.Content[i])
				cloned.Value = item.Value
				cloned.Tag = item.Tag
				if existing.Content[i].Style != yaml.Style(0) {
					cloned.Style = existing.Content[i].Style
				} else {
					cloned.Style = item.Style
				}
				out = cloned
			} else {
				copy := cloneNode(item)
				copyComments(existing.Content[i], copy)
				out = copy
			}
		}
		if out == nil {
			out = cloneNode(item)
		}
		merged.Content = append(merged.Content, out)
	}
	return merged
}

// mappingName extracts the value of the "name" key for mapping nodes.
func mappingName(n *yaml.Node) string {
	if n == nil || n.Kind != yaml.MappingNode {
		return ""
	}
	for i := 0; i+1 < len(n.Content); i += 2 {
		if n.Content[i].Value == "name" && n.Content[i+1].Kind == yaml.ScalarNode {
			return n.Content[i+1].Value
		}
	}
	return ""
}

// mergeMappingPreserveOrder updates dst (mapping) with the contents of src while keeping
// existing key ordering and comments from dst when keys overlap.
func mergeMappingPreserveOrder(dst, src *yaml.Node) {
	if dst == nil || src == nil || dst.Kind != yaml.MappingNode || src.Kind != yaml.MappingNode {
		return
	}
	kv := map[string]*yaml.Node{}
	for i := 0; i+1 < len(src.Content); i += 2 {
		kv[src.Content[i].Value] = cloneNode(src.Content[i+1])
	}
	seen := map[string]bool{}
	out := make([]*yaml.Node, 0, len(dst.Content)+len(kv))
	for i := 0; i+1 < len(dst.Content); i += 2 {
		keyNode := cloneNode(dst.Content[i])
		valNode := cloneNode(dst.Content[i+1])
		if replacement, ok := kv[keyNode.Value]; ok {
			copyComments(valNode, replacement)
			if valNode.Style != yaml.Style(0) && replacement.Kind == yaml.ScalarNode {
				replacement.Style = valNode.Style
			}
			valNode = replacement
			seen[keyNode.Value] = true
		}
		out = append(out, keyNode, valNode)
	}
	for k, v := range kv {
		if seen[k] {
			continue
		}
		out = append(out, &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: k}, v)
	}
	dst.Content = out
}

// cloneNode performs a shallow clone of a yaml.Node and its immediate children.
func cloneNode(n *yaml.Node) *yaml.Node {
	if n == nil {
		return nil
	}
	copy := *n
	if len(n.Content) > 0 {
		copy.Content = make([]*yaml.Node, len(n.Content))
		for i, c := range n.Content {
			copy.Content[i] = cloneNode(c)
		}
	}
	return &copy
}

func navigateParent(root *yaml.Node, tokens []string) (*yaml.Node, string) {
	if len(tokens) == 0 {
		return nil, ""
	}
	parentTokens := tokens[:len(tokens)-1]
	last := tokens[len(tokens)-1]
	parent := getNodeAt(root, parentTokens)
	return parent, last
}

func getNodeAt(root *yaml.Node, tokens []string) *yaml.Node {
	cur := root
	for _, t := range tokens {
		switch cur.Kind {
		case yaml.DocumentNode:
			if len(cur.Content) > 0 {
				cur = cur.Content[0]
				continue
			}
			return nil
		case yaml.MappingNode:
			found := false
			for i := 0; i < len(cur.Content); i += 2 {
				if cur.Content[i].Value == t {
					cur = cur.Content[i+1]
					found = true
					break
				}
			}
			if !found {
				return nil
			}
		case yaml.SequenceNode:
			idx := parseIndex(t, len(cur.Content))
			if idx < 0 || idx >= len(cur.Content) {
				return nil
			}
			cur = cur.Content[idx]
		default:
			return nil
		}
	}
	return cur
}

func parseIndex(s string, length int) int {
	if s == "-" {
		return length
	}
	var idx int
	fmt.Sscanf(s, "%d", &idx)
	return idx
}

func replaceOrAddMap(m *yaml.Node, key string, val *yaml.Node, allowAdd bool) {
	for i := 0; i < len(m.Content); i += 2 {
		if m.Content[i].Value == key {
			if val != nil && val.Kind == yaml.ScalarNode && val.Tag == "!!str" && val.Style == yaml.Style(0) {
				if m.Content[i+1].Kind == yaml.ScalarNode {
					val.Style = m.Content[i+1].Style
				}
			}
			m.Content[i+1] = val
			return
		}
	}
	if allowAdd {
		if val != nil && val.Kind == yaml.ScalarNode && val.Tag == "!!str" && val.Style == yaml.Style(0) {
			val.Style = yaml.DoubleQuotedStyle
		}
		m.Content = append(m.Content, &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}, val)
	}
}

func removeMapKey(m *yaml.Node, key string) {
	out := m.Content[:0]
	for i := 0; i < len(m.Content); i += 2 {
		if m.Content[i].Value == key {
			continue
		}
		out = append(out, m.Content[i], m.Content[i+1])
	}
	m.Content = out
}

func jsonToYAMLNode(data []byte) (*yaml.Node, error) {
	// JSON is a subset of YAML, so decode directly into a yaml.Node to retain
	// numeric types (ints stay ints) and avoid string quoting changes that occur
	// when round-tripping through interface{}.
	dec := yaml.NewDecoder(bytes.NewReader(data))
	dec.KnownFields(false)

	var n yaml.Node
	if err := dec.Decode(&n); err != nil {
		return nil, err
	}
	forceBlock(&n)
	normalizeScalarStyle(&n)
	if n.Kind == yaml.DocumentNode && len(n.Content) > 0 {
		return n.Content[0], nil
	}
	return &n, nil
}

// forceBlock clears flow style markers so sequences/maps render in block style.
func forceBlock(n *yaml.Node) {
	if n == nil {
		return
	}
	if n.Kind == yaml.SequenceNode || n.Kind == yaml.MappingNode {
		n.Style &^= yaml.FlowStyle
	}
	for _, c := range n.Content {
		forceBlock(c)
	}
}

// normalizeScalarStyle strips explicit quoting styles on scalars coming from JSON
// payloads so that string keys/values encode using plain scalars when safe.
func normalizeScalarStyle(n *yaml.Node) {
	if n == nil {
		return
	}
	if n.Kind == yaml.ScalarNode {
		switch n.Style {
		case yaml.DoubleQuotedStyle, yaml.SingleQuotedStyle:
			n.Style = 0
		}
	}
	for _, c := range n.Content {
		normalizeScalarStyle(c)
	}
}

// captureBlockScalars records the original textual content of folded/literal block scalars
// so we can restore their exact line breaks on marshal.
func captureBlockScalars(doc *yaml.Node, data []byte) map[*yaml.Node]blockInfo {
	lines := bytes.Split(data, []byte("\n"))
	out := map[*yaml.Node]blockInfo{}
	var walk func(n *yaml.Node)
	walk = func(n *yaml.Node) {
		if n == nil {
			return
		}
		if n.Kind == yaml.ScalarNode && (n.Style == yaml.FoldedStyle || n.Style == yaml.LiteralStyle) {
			lineIdx := n.Line - 1
			if lineIdx >= 0 && lineIdx+1 < len(lines) {
				contentIndent := leadingSpaces(lines[lineIdx+1])
				header := string(bytes.TrimRight(lines[lineIdx], "\r"))
				indent := leadingSpaces(lines[lineIdx])
				// gather subsequent lines until indentation shrinks
				var collected []string
				for i := lineIdx + 1; i < len(lines); i++ {
					l := lines[i]
					if len(bytes.TrimSpace(l)) == 0 {
						if leadingSpaces(l) < contentIndent {
							break
						}
						collected = append(collected, "")
						continue
					}
					if leadingSpaces(l) < contentIndent {
						break
					}
					trimmed := string(bytes.TrimRight(l[contentIndent:], "\r"))
					collected = append(collected, trimmed)
				}
				if len(collected) > 0 {
					var body strings.Builder
					pad := strings.Repeat(" ", contentIndent)
					for _, line := range collected {
						body.WriteString(pad)
						body.WriteString(line)
						body.WriteString("\n")
					}
					out[n] = blockInfo{header: header, body: body.String(), indent: indent}
				}
			}
		}
		for _, c := range n.Content {
			walk(c)
		}
	}
	walk(doc)
	return out
}

// normalizeEmptyMaps converts explicit null mapping values into empty maps so they render as {}.
func normalizeEmptyMaps(n *yaml.Node) {
	if n == nil {
		return
	}
	if n.Kind == yaml.MappingNode {
		for i := 0; i+1 < len(n.Content); i += 2 {
			v := n.Content[i+1]
			if v.Kind == yaml.ScalarNode && v.Tag == "!!null" && v.Value == "" {
				n.Content[i+1] = &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			}
			normalizeEmptyMaps(n.Content[i+1])
		}
	}
	for _, c := range n.Content {
		normalizeEmptyMaps(c)
	}
}

// ensureEmptyMapsFlow marks empty mapping nodes to render inline as {}.
func ensureEmptyMapsFlow(n *yaml.Node) {
	if n == nil {
		return
	}
	if n.Kind == yaml.MappingNode {
		if len(n.Content) == 0 {
			n.Style |= yaml.FlowStyle
		}
	}
	for _, c := range n.Content {
		ensureEmptyMapsFlow(c)
	}
}

func detectIndentlessSequences(data []byte) []indentlessInfo {
	lines := bytes.Split(data, []byte("\n"))
	var out []indentlessInfo
	for i := 0; i+1 < len(lines); i++ {
		line := lines[i]
		next := lines[i+1]
		trimmed := bytes.TrimSpace(line)
		if len(trimmed) == 0 || trimmed[len(trimmed)-1] != ':' {
			continue
		}
		key := strings.TrimSuffix(string(trimmed), ":")
		indent := leadingSpaces(line)
		nextIndent := leadingSpaces(next)
		if nextIndent != indent {
			continue
		}
		nextTrimmed := bytes.TrimSpace(next)
		if bytes.HasPrefix(nextTrimmed, []byte{'-'}) {
			out = append(out, indentlessInfo{key: key, indent: indent})
		}
	}
	return out
}

func restoreIndentlessSequences(data []byte, indent int, infos []indentlessInfo) []byte {
	if indent <= 0 {
		return data
	}
	lines := bytes.Split(data, []byte("\n"))
	for i := 0; i < len(lines); i++ {
		line := lines[i]
		lineIndent := leadingSpaces(line)
		trimmed := strings.TrimSpace(string(line))
		for _, info := range infos {
			if lineIndent == info.indent && trimmed == info.key+":" {
				for j := i + 1; j < len(lines); j++ {
					l := lines[j]
					if len(bytes.TrimSpace(l)) == 0 {
						continue
					}
					lIndent := leadingSpaces(l)
					if lIndent <= info.indent {
						break
					}
					if lIndent >= indent {
						lines[j] = dropIndent(l, indent)
					}
				}
				break
			}
		}
	}
	return bytes.Join(lines, []byte("\n"))
}

func captureCommentSpacing(data []byte) map[string]int {
	lines := bytes.Split(data, []byte("\n"))
	out := make(map[string]int)
	for _, l := range lines {
		idx := bytes.IndexByte(l, '#')
		if idx <= 0 {
			continue
		}
		spaces := 0
		for j := idx - 1; j >= 0 && l[j] == ' '; j-- {
			spaces++
		}
		comment := string(l[idx:])
		out[comment] = spaces
	}
	return out
}

func applyCommentSpacing(data []byte, spacing map[string]int) []byte {
	if len(spacing) == 0 {
		return data
	}
	lines := bytes.Split(data, []byte("\n"))
	for i, l := range lines {
		idx := bytes.IndexByte(l, '#')
		if idx <= 0 {
			continue
		}
		comment := string(l[idx:])
		want, ok := spacing[comment]
		if !ok {
			continue
		}
		spaces := 0
		for j := idx - 1; j >= 0 && l[j] == ' '; j-- {
			spaces++
		}
		if spaces == want {
			continue
		}
		trimEnd := idx - spaces
		if trimEnd < 0 {
			trimEnd = 0
		}
		nl := append([]byte(nil), l[:trimEnd]...)
		nl = append(nl, bytes.Repeat([]byte(" "), want)...)
		nl = append(nl, l[idx:]...)
		lines[i] = nl
	}
	return bytes.Join(lines, []byte("\n"))
}

func applyBlockScalarText(data []byte, blocks map[*yaml.Node]blockInfo) []byte {
	out := data
	for _, info := range blocks {
		header := info.header
		idx := bytes.Index(out, []byte(header+"\n"))
		if idx == -1 {
			continue
		}
		start := idx + len(header) + 1
		end := start
		for end < len(out) {
			nl := bytes.IndexByte(out[end:], '\n')
			if nl == -1 {
				end = len(out)
				break
			}
			line := out[end : end+nl]
			if len(bytes.TrimSpace(line)) == 0 {
				end += nl + 1
				continue
			}
			if leadingSpaces(line) <= info.indent {
				break
			}
			end += nl + 1
		}
		replacement := []byte(header + "\n" + info.body)
		merged := append([]byte{}, out[:idx]...)
		merged = append(merged, replacement...)
		merged = append(merged, out[end:]...)
		out = merged
	}
	return out
}

func dropIndent(line []byte, count int) []byte {
	if count <= 0 {
		return append([]byte(nil), line...)
	}
	idx := 0
	for idx < len(line) && idx < count && line[idx] == ' ' {
		idx++
	}
	return append([]byte(nil), line[idx:]...)
}

// detectIndent returns the minimal positive indentation observed in the data.
func detectIndent(data []byte) int {
	lines := bytes.Split(data, []byte("\n"))
	indent := 0
	for _, l := range lines {
		if len(l) == 0 {
			continue
		}
		c := leadingSpaces(l)
		if c == 0 {
			continue
		}
		if indent == 0 || c < indent {
			indent = c
		}
	}
	if indent == 0 {
		indent = 2
	}
	return indent
}

// leadingSpaces counts leading space characters.
func leadingSpaces(line []byte) int {
	i := 0
	for i < len(line) && line[i] == ' ' {
		i++
	}
	return i
}
