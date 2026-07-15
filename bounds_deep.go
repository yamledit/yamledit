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
				b, ok := boundsForMappingEntry(original, lineOffsets, k)
				if ok {
					b.anchor = v.Anchor
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
func boundsForMappingEntry(original []byte, lineOffsets []int, keyNode *yaml.Node) (kvBounds, bool) {
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

	end := len(original)
	for ln := keyNode.Line + 1; ln <= len(lineOffsets); ln++ {
		lineStart := lineOffsets[ln-1]
		lineEnd := len(original)
		if ln < len(lineOffsets) {
			lineEnd = lineOffsets[ln] // start of next line
		}
		raw := original[lineStart:lineEnd]

		trim := bytes.TrimSpace(raw)
		if len(trim) == 0 {
			continue // blank line
		}
		if trim[0] == '#' {
			// A same/less-indented standalone comment is safer to associate with
			// the following sibling (or document footer), not the key being
			// deleted. More-indented comments remain inside this key's subtree.
			if countLeadingIndent(raw) <= keyIndent {
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
