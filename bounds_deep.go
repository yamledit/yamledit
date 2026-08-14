package yamledit

import (
	"bytes"

	"gopkg.in/yaml.v3"
)

// indexBoundsByPathKeyDeep builds a fine-grained bounds index for EVERY mapping entry
// at every nesting level, including maps inside sequences.
//
// Path format matches yamledit’s internal pathKey format:
//   - mapping keys use the package's length-prefixed path encoding
//   - sequence indices are encoded as "[0]" segments (must match indexSeg / makeSeqPathKey)
func indexBoundsByPathKeyDeep(original []byte, doc *yaml.Node) (map[string][]kvBounds, map[string]struct{}, map[string]struct{}) {
	root := doc
	if root != nil && root.Kind == yaml.DocumentNode && len(root.Content) > 0 {
		root = root.Content[0]
	}

	// Reuse the same line-offset logic used elsewhere.
	lineOffsets := buildLineOffsets(original) // line N (1-based) => start byte offset
	out := make(map[string][]kvBounds, 128)
	unsafe := make(map[string]struct{})
	opaque := make(map[string]struct{})
	walkBoundsDeep(original, lineOffsets, root, nil, out, unsafe, opaque, false, false)
	return out, unsafe, opaque
}

// indexNonReproduciblePaths records addressable regions containing source
// syntax that yaml.v3 resolves into ordinary Node fields but cannot emit again.
// Keep this separate from opaque paths: live-AST rewriting is exactly what makes
// most opaque presentation safe, whereas a bare non-specific `!` property is
// absent from the live graph and must block automatic ancestor promotion.
func indexNonReproduciblePaths(original []byte, doc *yaml.Node) map[string]struct{} {
	root := doc
	if root != nil && root.Kind == yaml.DocumentNode && len(root.Content) > 0 {
		root = root.Content[0]
	}
	lineOffsets := buildLineOffsets(original)
	paths := make(map[string]struct{})
	mark := func(path []string) {
		for depth := 1; depth <= len(path); depth++ {
			paths[joinPath(path[:depth])] = struct{}{}
		}
	}
	var walk func(*yaml.Node, []string)
	walk = func(node *yaml.Node, path []string) {
		if node == nil {
			return
		}
		if nodeHasNonSpecificTag(original, lineOffsets, node) {
			mark(path)
		}
		switch node.Kind {
		case yaml.MappingNode:
			for index := 0; index+1 < len(node.Content); index += 2 {
				key, value := node.Content[index], node.Content[index+1]
				if key == nil || key.Kind != yaml.ScalarNode {
					continue
				}
				childPath := append(append([]string(nil), path...), key.Value)
				if nodeHasNonSpecificTag(original, lineOffsets, key) {
					mark(childPath)
				}
				walk(value, childPath)
			}
		case yaml.SequenceNode:
			for index, child := range node.Content {
				childPath := append(append([]string(nil), path...), indexSeg(index))
				walk(child, childPath)
			}
		}
	}
	walk(root, nil)
	return paths
}

func walkBoundsDeep(original []byte, lineOffsets []int, node *yaml.Node, prefix []string, out map[string][]kvBounds, unsafe, opaque map[string]struct{}, inheritedUnsafe, insideFlow bool) {
	if node == nil {
		return
	}
	// The byte-boundary logic below is deliberately block-style. Flow
	// collections can place several keys/items on one line; indexing them as
	// independent line ranges causes overlapping patches and data loss. We must
	// still walk their children, though: ancestor rewrites use a metadata-free
	// logical shadow and would otherwise drop tags, anchors, and aliases hidden
	// inside a flow collection.
	flowContext := insideFlow || node.Style&yaml.FlowStyle != 0
	switch node.Kind {
	case yaml.MappingNode:
		keyCounts := make(map[string]int)
		for i := 0; i+1 < len(node.Content); i += 2 {
			key := node.Content[i]
			if key != nil && key.Kind == yaml.ScalarNode {
				keyCounts[key.Tag+"\x00"+key.Value]++
			}
		}
		// Content: k0, v0, k1, v1, ...
		for i := 0; i+1 < len(node.Content); i += 2 {
			k := node.Content[i]
			v := node.Content[i+1]

			if k == nil {
				continue
			}
			if k.Kind != yaml.ScalarNode {
				// Complex YAML keys cannot be represented in the JSON-shaped ordered
				// shadow. They also have no addressable path segment to recurse through,
				// so make every addressable owner opaque instead of silently dropping
				// the key during an ancestor rewrite.
				for depth := 1; depth <= len(prefix); depth++ {
					opaque[joinPath(prefix[:depth])] = struct{}{}
				}
				continue
			}

			pk := makePathKey(prefix, k.Value)
			if inheritedUnsafe || flowContext {
				unsafe[pk] = struct{}{}
			}
			markOpaque := func() {
				for depth := 1; depth <= len(prefix); depth++ {
					opaque[joinPath(prefix[:depth])] = struct{}{}
				}
			}
			// JSON/YAML editing APIs address mapping members by string. A scalar
			// key such as the integer 1 is distinct from the string "1" in YAML,
			// but both have the same textual Node.Value. Treat that path as
			// ambiguous so duplicate cleanup or replacement cannot collapse the
			// two keys.
			nonStringKey := k.Tag != "" && k.Tag != "!!str"
			// Explicit mapping keys use a separate "? key" / ": value" form and
			// cannot be represented by this line-oriented bound safely, regardless
			// of whether their value is scalar, mapping, or sequence-valued.
			explicitKey := !flowContext && isExplicitMappingKeyLine(original, lineOffsets, k)
			dashOwned := !flowContext && mappingKeyOwnsSequenceDash(original, lineOffsets, k)
			if nodeCarriesSourceMetadata(k, true) || nodeCarriesSourceMetadata(v, false) {
				markOpaque()
			}
			if explicitKey || dashOwned || nonStringKey {
				unsafe[pk] = struct{}{}
			} else if !flowContext {
				b, ok := boundsForMappingEntry(original, lineOffsets, k, v)
				if ok {
					b.anchor = v.Anchor
					// yaml.v3 recognizes comments immediately following a completed
					// flow collection or quoted scalar even without intervening space.
					// Preserve parser metadata for this entry line instead of asking the
					// lightweight scanner to guess whether an embedded '#' starts a
					// comment. A collection value may also carry a comment from a later
					// child line, which must not be hoisted onto the key line.
					if k.LineComment != "" {
						b.lineComment = k.LineComment
					} else if v.Line == k.Line {
						b.lineComment = v.LineComment
					}
					if (v.Kind == yaml.MappingNode && v.Tag != "!!map") || (v.Kind == yaml.SequenceNode && v.Tag != "!!seq") {
						b.collectionTag = v.Tag
					}
					out[pk] = append(out[pk], b)
				}
			}
			if v.Kind == yaml.SequenceNode {
				for _, item := range v.Content {
					if item == nil {
						continue
					}
					if nodeCarriesSourceMetadata(item, false) {
						// Shape rewrites currently render sequence items from the
						// logical view, which has no anchor/tag metadata. Mark the
						// owning sequence ambiguous so such rewrites fail safely.
						fullPath := append(append([]string(nil), prefix...), k.Value)
						for depth := 1; depth <= len(fullPath); depth++ {
							unsafe[joinPath(fullPath[:depth])] = struct{}{}
						}
						break
					}
				}
			}

			// Recurse into value to index deeper keys.
			nextPrefix := append(append([]string(nil), prefix...), k.Value)
			duplicateAncestor := keyCounts[k.Tag+"\x00"+k.Value] > 1
			walkBoundsDeep(original, lineOffsets, v, nextPrefix, out, unsafe, opaque, inheritedUnsafe || duplicateAncestor, flowContext)
		}
	case yaml.SequenceNode:
		for idx, child := range node.Content {
			nextPrefix := append(append([]string(nil), prefix...), indexSeg(idx))
			if nodeCarriesSourceMetadata(child, false) {
				for depth := 1; depth <= len(prefix); depth++ {
					opaque[joinPath(prefix[:depth])] = struct{}{}
				}
			}
			walkBoundsDeep(original, lineOffsets, child, nextPrefix, out, unsafe, opaque, inheritedUnsafe, flowContext)
		}
	case yaml.DocumentNode:
		if len(node.Content) > 0 {
			walkBoundsDeep(original, lineOffsets, node.Content[0], prefix, out, unsafe, opaque, inheritedUnsafe, flowContext)
		}
	default:
		// Scalars / aliases: nothing to index at this node.
	}
}

func nodeCarriesSourceMetadata(node *yaml.Node, key bool) bool {
	if node == nil {
		return false
	}
	if node.Kind == yaml.AliasNode {
		return true
	}
	// Anchors and explicit/custom tags affect YAML semantics but are absent from
	// the ordered logical shadow used by ancestor rewrites. Comments and scalar
	// style are intentionally not treated as opaque here: some supported delete
	// operations remove the commented/styled node itself.
	if node.Anchor != "" {
		return true
	}
	if key {
		return node.Kind != yaml.ScalarNode || node.Tag != "!!str"
	}
	if node.Kind == yaml.ScalarNode {
		switch node.Tag {
		case "", "!!str", "!!null", "!!bool", "!!int", "!!float":
			return false
		default:
			return true
		}
	}
	defaultTag := "!!map"
	if node.Kind == yaml.SequenceNode {
		defaultTag = "!!seq"
	}
	return node.Tag != "" && node.Tag != defaultTag
}

// markLivePresentationOpaquePaths records containers whose current AST still
// contains comments or scalar spelling that the ordered logical shadow cannot
// reproduce. It runs at Marshal time, after edits: metadata on a node that was
// intentionally deleted is therefore absent and does not block that deletion,
// while metadata on an untouched sibling prevents a lossy ancestor rewrite.
func markLivePresentationOpaquePaths(node *yaml.Node, prefix []string, opaque map[string]struct{}) {
	if node == nil {
		return
	}
	markAncestors := func(path []string) {
		for depth := 1; depth < len(path); depth++ {
			opaque[joinPath(path[:depth])] = struct{}{}
		}
	}
	hasPresentation := func(n *yaml.Node) bool {
		if n == nil {
			return false
		}
		if n.HeadComment != "" || n.LineComment != "" || n.FootComment != "" {
			return true
		}
		return n.Kind == yaml.ScalarNode &&
			n.Style&(yaml.SingleQuotedStyle|yaml.DoubleQuotedStyle|yaml.LiteralStyle|yaml.FoldedStyle) != 0
	}

	if hasPresentation(node) {
		markAncestors(prefix)
	}
	switch node.Kind {
	case yaml.DocumentNode:
		if len(node.Content) > 0 {
			markLivePresentationOpaquePaths(node.Content[0], prefix, opaque)
		}
	case yaml.MappingNode:
		for i := 0; i+1 < len(node.Content); i += 2 {
			key, value := node.Content[i], node.Content[i+1]
			if key == nil || key.Kind != yaml.ScalarNode {
				continue
			}
			next := append(append([]string(nil), prefix...), key.Value)
			// Re-rendering an entire entry from the ordered shadow cannot preserve
			// presentation attached to the key node itself. Scalar token surgery is
			// still safe because it leaves the key bytes untouched; structural
			// rewrites must fail or promote rather than silently drop this metadata.
			if key.Anchor != "" || key.Style != 0 ||
				(key.Tag != "" && key.Tag != "!!str") || key.HeadComment != "" || key.FootComment != "" {
				opaque[joinPath(next)] = struct{}{}
			}
			if hasPresentation(key) {
				markAncestors(next)
			}
			markLivePresentationOpaquePaths(value, next, opaque)
		}
	case yaml.SequenceNode:
		for index, child := range node.Content {
			next := append(append([]string(nil), prefix...), indexSeg(index))
			markLivePresentationOpaquePaths(child, next, opaque)
		}
	}
}

func isExplicitMappingKeyLine(original []byte, lineOffsets []int, keyNode *yaml.Node) bool {
	if keyNode == nil || keyNode.Line <= 0 {
		return false
	}
	start := lineStartOffset(lineOffsets, keyNode.Line)
	if start < 0 || start >= len(original) {
		return false
	}
	end := findLineEnd(original, start)
	if end < start {
		return false
	}
	line := bytes.TrimPrefix(original[start:min(end+1, len(original))], []byte{0xef, 0xbb, 0xbf})
	line = bytes.TrimLeft(line, " \t")
	if len(line) > 1 && line[0] == '-' && (line[1] == ' ' || line[1] == '\t') {
		line = bytes.TrimLeft(line[2:], " \t")
	}
	if len(line) > 0 && line[0] == '?' && (len(line) == 1 || line[1] == ' ' || line[1] == '\t' || line[1] == '\r' || line[1] == '\n') {
		return true
	}

	// In the multiline explicit-key form, yaml.v3 points at the content line
	// rather than the preceding standalone `?` indicator.
	for previous := keyNode.Line - 1; previous >= 1; previous-- {
		previousStart := lineStartOffset(lineOffsets, previous)
		if previousStart < 0 || previousStart >= len(original) {
			break
		}
		previousEnd := findLineEnd(original, previousStart)
		candidate := bytes.TrimPrefix(original[previousStart:min(previousEnd+1, len(original))], []byte{0xef, 0xbb, 0xbf})
		candidate = bytes.TrimSpace(candidate)
		if len(candidate) == 0 || candidate[0] == '#' {
			continue
		}
		if len(candidate) > 1 && candidate[0] == '-' && (candidate[1] == ' ' || candidate[1] == '\t') {
			candidate = bytes.TrimSpace(candidate[2:])
		}
		return len(candidate) > 0 && candidate[0] == '?' &&
			(len(candidate) == 1 || candidate[1] == ' ' || candidate[1] == '\t' || candidate[1] == '#')
	}
	return false
}

func mappingKeyOwnsSequenceDash(original []byte, lineOffsets []int, keyNode *yaml.Node) bool {
	if keyNode == nil || keyNode.Line <= 0 {
		return false
	}
	start := lineStartOffset(lineOffsets, keyNode.Line)
	if start < 0 || start >= len(original) {
		return false
	}
	end := findLineEnd(original, start)
	if end < start {
		return false
	}
	line := bytes.TrimPrefix(original[start:min(end+1, len(original))], []byte{0xef, 0xbb, 0xbf})
	line = bytes.TrimLeft(line, " \t")
	return len(line) > 1 && line[0] == '-' && (line[1] == ' ' || line[1] == '\t')
}

// boundsForMappingEntry returns the byte-span covering the *entire key region* for the given key:
// from the start of the key’s line up to (but not including) the next sibling/parent line.
//
// This is what lets structuralRewrite replace ONLY "…/properties/groupId" rather than the whole
// "pipelineProcess" block.
func boundsForMappingEntry(original []byte, lineOffsets []int, keyNode, valueNode *yaml.Node) (kvBounds, bool) {
	if keyNode == nil || keyNode.Line <= 0 {
		return kvBounds{}, false
	}
	if keyNode.Line-1 >= len(lineOffsets) {
		return kvBounds{}, false
	}

	start := lineOffsets[keyNode.Line-1]
	if keyNode.Line == 1 && start == 0 && len(original) >= 3 && bytes.Equal(original[:3], []byte{0xef, 0xbb, 0xbf}) {
		start = 3
	}
	keyIndent := keyNode.Column - 1 // important for "- key: ..." cases
	// normalizeImplicitMaps represents a bare `key:` as an empty block-style
	// mapping. It has no source subtree of its own, so an indented standalone
	// comment after the key must not be swallowed when the bare token is rewritten
	// to `{}`. yaml.v3 commonly attaches that comment to the following key.
	implicitEmptyMap := valueNode != nil && valueNode.Kind == yaml.MappingNode &&
		len(valueNode.Content) == 0 && valueNode.Style&yaml.FlowStyle == 0
	// Indentation normally identifies the next sibling, but YAML permits quoted
	// scalars and flow collections to continue at any column. A continuation such
	// as the second line below is still part of `value`, even though it begins at
	// the same indentation as a top-level key:
	//
	//   value: "first
	//   looks: like-a-key"
	//
	// The same applies to `{ ... }` / `[ ... ]`, including those nested inside a
	// block sequence. Never terminate a key region before every explicitly
	// delimited token in its value subtree has closed.
	mandatoryEnd := sourceDelimitedSubtreeEnd(original, lineOffsets, valueNode)

	end := len(original)
	for ln := keyNode.Line + 1; ln <= len(lineOffsets); ln++ {
		lineStart := lineOffsets[ln-1]
		lineEnd := len(original)
		if ln < len(lineOffsets) {
			lineEnd = lineOffsets[ln] // start of next line
		}
		raw := original[lineStart:lineEnd]
		if lineStart < mandatoryEnd {
			continue
		}

		trim := bytes.TrimSpace(raw)
		if len(trim) == 0 {
			continue // blank line
		}
		if trim[0] == '#' {
			// A same/less-indented standalone comment is safer to associate with
			// the following sibling (or document footer), not the key being
			// deleted. More-indented comments remain inside this key's subtree.
			if implicitEmptyMap || countLeadingIndent(raw) <= keyIndent {
				end = lineStart
				break
			}
			continue
		}

		indent := countLeadingIndent(raw)

		// If this line is a sequence item ("<indent>- ..."), the *key* (if any) effectively
		// starts at indent+2 (after "- ").
		effIndent := indent
		if len(raw) > indent+1 && raw[indent] == '-' && (raw[indent+1] == ' ' || raw[indent+1] == '\t') {
			effIndent = indent + 2
		}

		// Anything at the same or lower indentation ends this key’s region.
		if effIndent <= keyIndent {
			end = lineStart
			break
		}
	}

	return kvBounds{start: start, end: end}, true
}

// sourceDelimitedSubtreeEnd returns the furthest exclusive byte offset occupied
// by a source token whose closing boundary cannot be inferred from indentation:
// quoted scalars, flow collections, and block scalars. A block mapping/sequence
// may contain one of these values, so inspect the whole subtree. The returned
// offset is a lower bound only; boundsForMappingEntry still uses indentation to
// include ordinary block children and to stop before the next sibling.
func sourceDelimitedSubtreeEnd(original []byte, lineOffsets []int, root *yaml.Node) int {
	maxEnd := 0
	seen := make(map[*yaml.Node]struct{})
	var walk func(*yaml.Node)
	walk = func(node *yaml.Node) {
		if node == nil {
			return
		}
		if _, ok := seen[node]; ok {
			return
		}
		seen[node] = struct{}{}
		if end, ok := sourceDelimitedNodeEnd(original, lineOffsets, node); ok && end > maxEnd {
			maxEnd = end
		}
		for _, child := range node.Content {
			walk(child)
		}
	}
	walk(root)
	return maxEnd
}

func sourceDelimitedNodeEnd(original []byte, lineOffsets []int, node *yaml.Node) (int, bool) {
	if node == nil || len(original) == 0 {
		return 0, false
	}
	pos := offsetFor(original, lineOffsets, node.Line, node.Column)
	if pos < 0 || pos >= len(original) {
		return 0, false
	}
	pos = skipYAMLNodeProperties(original, pos)
	if pos < 0 || pos >= len(original) {
		return 0, false
	}

	if node.Kind == yaml.ScalarNode {
		switch {
		case node.Style&yaml.SingleQuotedStyle != 0 && original[pos] == '\'':
			return scanYAMLSingleQuotedEnd(original, pos)
		case node.Style&yaml.DoubleQuotedStyle != 0 && original[pos] == '"':
			return scanYAMLDoubleQuotedEnd(original, pos)
		case node.Style&(yaml.LiteralStyle|yaml.FoldedStyle) != 0:
			lineStart := lineStartOffset(lineOffsets, node.Line)
			lineEnd := findLineEnd(original, lineStart)
			if lineStart < 0 || lineStart >= len(original) || lineEnd < lineStart {
				return 0, false
			}
			keyIndent := countLeadingIndent(original[lineStart:min(lineEnd+1, len(original))])
			end := extendScalarBlockEnd(original, lineOffsets, node.Line, keyIndent)
			if end >= 0 && end < len(original) {
				return end + 1, true
			}
		}
		return 0, false
	}

	if node.Style&yaml.FlowStyle == 0 || (node.Kind != yaml.MappingNode && node.Kind != yaml.SequenceNode) {
		return 0, false
	}
	want := byte('{')
	if node.Kind == yaml.SequenceNode {
		want = '['
	}
	if original[pos] != want {
		return 0, false
	}
	return scanYAMLFlowCollectionEnd(original, pos)
}

// yaml.v3 reports a node's column at its first tag/anchor property. Advance to
// the actual scalar/collection token, allowing properties to be separated by
// comments and physical lines.
func skipYAMLNodeProperties(original []byte, pos int) int {
	for {
		for pos < len(original) {
			switch original[pos] {
			case ' ', '\t', '\r', '\n':
				pos++
			case '#':
				for pos < len(original) && original[pos] != '\n' {
					pos++
				}
			default:
				goto token
			}
		}
		return pos

	token:
		if original[pos] != '&' && original[pos] != '!' {
			return pos
		}
		if original[pos] == '!' && pos+1 < len(original) && original[pos+1] == '<' {
			close := bytes.IndexByte(original[pos+2:], '>')
			if close < 0 {
				return len(original)
			}
			pos += close + 3
			continue
		}
		pos++
		for pos < len(original) {
			switch original[pos] {
			case ' ', '\t', '\r', '\n', ',', '[', ']', '{', '}':
				goto nextProperty
			default:
				pos++
			}
		}
		return pos
	nextProperty:
	}
}

func scanYAMLSingleQuotedEnd(original []byte, start int) (int, bool) {
	for pos := start + 1; pos < len(original); pos++ {
		if original[pos] != '\'' {
			continue
		}
		if pos+1 < len(original) && original[pos+1] == '\'' {
			pos++
			continue
		}
		return pos + 1, true
	}
	return 0, false
}

func scanYAMLDoubleQuotedEnd(original []byte, start int) (int, bool) {
	escaped := false
	for pos := start + 1; pos < len(original); pos++ {
		if escaped {
			escaped = false
			continue
		}
		switch original[pos] {
		case '\\':
			escaped = true
		case '"':
			return pos + 1, true
		}
	}
	return 0, false
}

func scanYAMLFlowCollectionEnd(original []byte, start int) (int, bool) {
	stack := []byte{original[start]}
	inSingle, inDouble, escaped, inComment := false, false, false, false
	for pos := start + 1; pos < len(original); pos++ {
		ch := original[pos]
		if inComment {
			if ch == '\n' {
				inComment = false
			}
			continue
		}
		if inDouble {
			if escaped {
				escaped = false
				continue
			}
			if ch == '\\' {
				escaped = true
			} else if ch == '"' {
				inDouble = false
			}
			continue
		}
		if inSingle {
			if ch == '\'' {
				if pos+1 < len(original) && original[pos+1] == '\'' {
					pos++
				} else {
					inSingle = false
				}
			}
			continue
		}

		switch ch {
		case '"':
			inDouble = true
		case '\'':
			inSingle = true
		case '#':
			if pos == 0 || original[pos-1] == ' ' || original[pos-1] == '\t' || original[pos-1] == '\r' || original[pos-1] == '\n' || original[pos-1] == ',' {
				inComment = true
			}
		case '!':
			// Delimiters are legal inside a verbatim tag URI and must not affect
			// collection depth.
			if pos+1 < len(original) && original[pos+1] == '<' {
				if close := bytes.IndexByte(original[pos+2:], '>'); close >= 0 {
					pos += close + 2
				}
			}
		case '{', '[':
			stack = append(stack, ch)
		case '}', ']':
			if len(stack) == 0 || (ch == '}' && stack[len(stack)-1] != '{') || (ch == ']' && stack[len(stack)-1] != '[') {
				return 0, false
			}
			stack = stack[:len(stack)-1]
			if len(stack) == 0 {
				return pos + 1, true
			}
		}
	}
	return 0, false
}

func countLeadingIndent(line []byte) int {
	n := 0
	for n < len(line) {
		switch line[n] {
		case ' ':
			n++
		case '\t':
			// YAML forbids tabs for indentation, but treat as 1 to avoid panics.
			n++
		default:
			return n
		}
	}
	return n
}
