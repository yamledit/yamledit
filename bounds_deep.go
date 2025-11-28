package yamledit

import (
	"bytes"

	"gopkg.in/yaml.v3"
)

// indexBoundsByPathKeyDeep builds a fine-grained bounds index for EVERY mapping entry
// at every nesting level, including maps inside sequences.
//
// Path format matches yamledit’s internal pathKey format:
//   - mapping keys are separated by pathSep
//   - sequence indices are encoded as "[0]" segments (must match indexSeg / makeSeqPathKey)
func indexBoundsByPathKeyDeep(original []byte, doc *yaml.Node) map[string][]kvBounds {
	root := doc
	if root != nil && root.Kind == yaml.DocumentNode && len(root.Content) > 0 {
		root = root.Content[0]
	}

	// Reuse the same line-offset logic used elsewhere.
	lineOffsets := buildLineOffsets(original) // line N (1-based) => start byte offset
	out := make(map[string][]kvBounds, 128)
	walkBoundsDeep(original, lineOffsets, root, nil, out)
	return out
}

func walkBoundsDeep(original []byte, lineOffsets []int, node *yaml.Node, prefix []string, out map[string][]kvBounds) {
	if node == nil {
		return
	}
	switch node.Kind {
	case yaml.MappingNode:
		// Content: k0, v0, k1, v1, ...
		for i := 0; i+1 < len(node.Content); i += 2 {
			k := node.Content[i]
			v := node.Content[i+1]

			if k == nil || k.Kind != yaml.ScalarNode {
				continue
			}

			pk := makePathKey(prefix, k.Value)
			if b, ok := boundsForMappingEntry(original, lineOffsets, k); ok {
				out[pk] = append(out[pk], b)
			}

			// Recurse into value to index deeper keys.
			nextPrefix := append(append([]string(nil), prefix...), k.Value)
			walkBoundsDeep(original, lineOffsets, v, nextPrefix, out)
		}
	case yaml.SequenceNode:
		for idx, child := range node.Content {
			nextPrefix := append(append([]string(nil), prefix...), indexSeg(idx))
			walkBoundsDeep(original, lineOffsets, child, nextPrefix, out)
		}
	case yaml.DocumentNode:
		if len(node.Content) > 0 {
			walkBoundsDeep(original, lineOffsets, node.Content[0], prefix, out)
		}
	default:
		// Scalars / aliases: nothing to index at this node.
	}
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
			continue // comment-only line
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
