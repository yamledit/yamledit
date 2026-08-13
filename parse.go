package yamledit

import (
	"bytes"
	"fmt"
	"io"
	"weak"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// decodeSingleYAMLDocument decodes exactly one YAML document. yaml.Unmarshal
// accepts a stream and stops after its first document, which can hide a valid
// second document or malformed trailing content from callers that expect this
// package to edit one mapping document.
func decodeSingleYAMLDocument(data []byte, doc *yaml.Node) error {
	dec := yaml.NewDecoder(bytes.NewReader(data))
	if err := dec.Decode(doc); err != nil {
		return err
	}

	var trailing yaml.Node
	switch err := dec.Decode(&trailing); {
	case err == io.EOF:
		return nil
	case err != nil:
		return fmt.Errorf("invalid trailing YAML content: %w", err)
	default:
		return fmt.Errorf("multiple YAML documents are not supported")
	}
}

func isYAMLTriviaOnly(data []byte) bool {
	data = bytes.TrimPrefix(data, []byte{0xef, 0xbb, 0xbf})
	for _, line := range bytes.Split(data, []byte{'\n'}) {
		line = bytes.TrimSpace(line)
		if len(line) != 0 && line[0] != '#' {
			return false
		}
	}
	return true
}

// normalizeImplicitMaps preserves the package's established convenience that
// a bare mapping value (`key:`) behaves as an empty mapping. Restrict the
// coercion to implicit nulls inside ordinary maps: explicit !!null values and
// null-shaped entries used by semantic mapping types such as !!set must retain
// their YAML meaning.
func normalizeImplicitMaps(doc *yaml.Node, st *docState) {
	if doc == nil || st == nil || doc.Kind != yaml.DocumentNode || len(doc.Content) == 0 {
		return
	}
	var walk func(*yaml.Node, []ptrToken)
	walk = func(node *yaml.Node, path []ptrToken) {
		if node == nil {
			return
		}
		switch node.Kind {
		case yaml.MappingNode:
			if node.Tag != "" && node.Tag != "!!map" {
				return
			}
			for i := 0; i+1 < len(node.Content); i += 2 {
				key, value := node.Content[i], node.Content[i+1]
				if key == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
					continue
				}
				if value.Kind == yaml.ScalarNode && value.Tag == "!!null" && value.Value == "" &&
					value.Anchor == "" && !scalarHasExplicitTag(st.original, st.lineOffsets, value) {
					replacement := &yaml.Node{
						Kind:        yaml.MappingNode,
						Tag:         "!!map",
						HeadComment: value.HeadComment,
						LineComment: value.LineComment,
						FootComment: value.FootComment,
						Line:        value.Line,
						Column:      value.Column,
					}
					node.Content[i+1] = replacement
					fullPath := append(append([]ptrToken(nil), path...), ptrToken{key: key.Value})
					if updated, err := setOrderedAtPath(st.ordered, fullPath, gyaml.MapSlice{}); err == nil {
						st.ordered = updated
					}
					continue
				}
				walk(value, append(path, ptrToken{key: key.Value}))
			}
		case yaml.SequenceNode:
			for index, child := range node.Content {
				walk(child, append(path, ptrToken{isIdx: true, index: index}))
			}
		}
	}
	walk(doc.Content[0], nil)
}

// Parse reads YAML data and returns a yaml.Node, creating a minimal mapping document if empty.
func Parse(data []byte) (*yaml.Node, error) {
	for i, b := range data {
		if b == '\r' && (i+1 >= len(data) || data[i+1] != '\n') {
			return nil, fmt.Errorf("yamledit: failed to parse YAML: lone carriage-return line endings are unsupported")
		}
	}
	doc := &yaml.Node{
		Kind:    yaml.DocumentNode,
		Content: []*yaml.Node{{Kind: yaml.MappingNode, Tag: "!!map"}},
	}

	if len(data) > 0 {
		var tmp yaml.Node
		if err := decodeSingleYAMLDocument(data, &tmp); err != nil {
			if err != io.EOF || !isYAMLTriviaOnly(data) {
				return nil, fmt.Errorf("yamledit: failed to parse YAML: %w", err)
			}
		} else {
			if tmp.Kind != yaml.DocumentNode || len(tmp.Content) == 0 || tmp.Content[0].Kind != yaml.MappingNode {
				return nil, fmt.Errorf("yamledit: top-level YAML is not a mapping")
			}
			doc = &tmp
		}
	}

	// Build shadow state using goccy/go-yaml (to preserve comments and ordered map for fallback)
	st := &docState{
		doc:                weak.Make(doc),
		comments:           gyaml.CommentMap{},
		ordered:            gyaml.MapSlice{},
		subPathByHN:        map[weak.Pointer[yaml.Node]][]string{},
		indent:             2,
		indentSeq:          true,
		original:           append([]byte(nil), data...),
		originalRootEmpty:  len(data) > 0 && doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 && doc.Content[0].Kind == yaml.MappingNode && len(doc.Content[0].Content) == 0,
		originalTriviaOnly: len(data) > 0 && isYAMLTriviaOnly(data),
		lineOffsets:        buildLineOffsets(data),
		mapIndex:           map[string]*mapInfo{},
		valueOccByPathKey:  map[string][]valueOcc{},
		boundsByPathKey:    map[string][]kvBounds{}, // Initialize new map
		unsafePathKeys:     map[string]struct{}{},
		opaquePathKeys:     map[string]struct{}{},
		seqIndex:           map[string]*seqInfo{},
		forceScalarRewrite: map[string]struct{}{},
		forceScalarTags:    map[string]string{},
		nodeRewriteIntents: map[string]nodeRewriteIntent{},
		toDelete:           map[string]struct{}{},
	}
	if st.originalRootEmpty {
		root := doc.Content[0]
		start := offsetFor(data, st.lineOffsets, root.Line, root.Column)
		if start >= 0 && start < len(data) {
			if open := bytes.IndexByte(data[start:], '{'); open >= 0 {
				open += start
				if close := bytes.IndexByte(data[open+1:], '}'); close >= 0 {
					close += open + 1
					if !bytes.Contains(data[open+1:close], []byte{'#'}) {
						st.rootTokenStart, st.rootTokenEnd = open, close+1
					}
				}
			}
		}
	}

	// Decode into ordered map and capture comments; detect indent and sequence style
	if len(data) > 0 {
		shadowData := bytes.TrimPrefix(data, []byte{0xef, 0xbb, 0xbf})
		if err := gyaml.UnmarshalWithOptions(shadowData, &st.ordered, gyaml.UseOrderedMap(), gyaml.CommentToMap(st.comments)); err == nil {
			ind, seq := detectIndentAndSequence(data)
			st.indent, st.indentSeq = ind, seq
		} else {
			// goccy rejects some YAML accepted by yaml.v3 (notably duplicate
			// keys). An empty shadow makes later edits invent empty mappings and
			// lose unrelated data, so build an ordered logical view from the AST.
			shadow, shadowErr := yamlNodeToOrderedValue(doc.Content[0])
			if shadowErr != nil {
				return nil, fmt.Errorf("yamledit: failed to build ordered YAML view: %w", shadowErr)
			}
			if ordered, ok := shadow.(gyaml.MapSlice); ok {
				st.ordered = ordered
			}
			ind, seq := detectIndentAndSequence(data)
			st.indent, st.indentSeq = ind, seq
		}
	}

	// goccy may use shared backing storage for an anchor target and the logical
	// expansion of its aliases. Detach the live shadow before edits so changing
	// the target cannot accidentally mutate an alias entry (or vice versa).
	st.ordered = cloneMapSlice(st.ordered)

	// Keep a snapshot of the original ordered map for diffing
	st.origOrdered = cloneMapSlice(st.ordered)

	normalizeImplicitMaps(doc, st)
	st.originalAST = cloneYAMLNodeGraph(doc)
	st.expectedAST = cloneYAMLNodeGraph(doc)

	// Index mapping handles (for path lookups later on)
	if doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 && doc.Content[0].Kind == yaml.MappingNode {
		st.subPathByHN[weak.Make(doc.Content[0])] = nil
		indexMappingHandles(st, doc.Content[0], nil)

		// Build byte-surgical indices off the original parsed tree
		if len(data) > 0 {
			indexPositions(st, doc.Content[0], nil)
		}
	}

	// Build a fine-grained bounds index for every mapping entry at every nesting level,
	// including mapping entries inside sequences. This is what allows structuralRewrite
	// to patch ONLY the changed key (e.g. groupId) without re-encoding sibling block scalars.
	if len(data) > 0 {
		st.boundsByPathKey, st.unsafePathKeys, st.opaquePathKeys = indexBoundsByPathKeyDeep(st.original, doc)
	}

	register(doc, st)
	return doc, nil
}

const orderedShadowNodeBudget = 100_000

func yamlNodeToOrderedValue(node *yaml.Node) (interface{}, error) {
	budget := orderedShadowNodeBudget
	return yamlNodeToOrderedValueSeen(node, make(map[*yaml.Node]bool), &budget)
}

func yamlNodeToOrderedValueSeen(node *yaml.Node, visiting map[*yaml.Node]bool, budget *int) (interface{}, error) {
	if node == nil {
		return nil, nil
	}
	if budget == nil || *budget <= 0 {
		return nil, fmt.Errorf("ordered shadow exceeds alias expansion limit of %d nodes", orderedShadowNodeBudget)
	}
	*budget = *budget - 1
	if visiting[node] {
		// Recursive aliases are valid YAML graphs but cannot be represented by
		// the acyclic ordered shadow. Keep a nil placeholder instead of recursing
		// until stack exhaustion; unsupported edits will safely fall back/error.
		return nil, nil
	}
	visiting[node] = true
	defer delete(visiting, node)
	switch node.Kind {
	case yaml.DocumentNode:
		if len(node.Content) == 0 {
			return gyaml.MapSlice{}, nil
		}
		if len(node.Content) != 1 || node.Content[0] == nil {
			return nil, fmt.Errorf("malformed YAML document node")
		}
		return yamlNodeToOrderedValueSeen(node.Content[0], visiting, budget)
	case yaml.MappingNode:
		if len(node.Content)%2 != 0 {
			return nil, fmt.Errorf("malformed YAML mapping node")
		}
		out := make(gyaml.MapSlice, 0, len(node.Content)/2)
		for i := 0; i+1 < len(node.Content); i += 2 {
			key := node.Content[i]
			if key == nil || node.Content[i+1] == nil {
				return nil, fmt.Errorf("malformed YAML mapping node")
			}
			if key.Kind != yaml.ScalarNode {
				return nil, fmt.Errorf("YAML mapping has a non-scalar key")
			}
			value, err := yamlNodeToOrderedValueSeen(node.Content[i+1], visiting, budget)
			if err != nil {
				return nil, err
			}
			out = append(out, gyaml.MapItem{Key: key.Value, Value: value})
		}
		return out, nil
	case yaml.SequenceNode:
		out := make([]interface{}, 0, len(node.Content))
		for _, child := range node.Content {
			if child == nil {
				return nil, fmt.Errorf("malformed YAML sequence node")
			}
			value, err := yamlNodeToOrderedValueSeen(child, visiting, budget)
			if err != nil {
				return nil, err
			}
			out = append(out, value)
		}
		return out, nil
	case yaml.AliasNode:
		return yamlNodeToOrderedValueSeen(node.Alias, visiting, budget)
	case yaml.ScalarNode:
		value := yamlNodeToInterface(node)
		if _, unresolved := value.(string); unresolved && (node.Tag == "!!int" || node.Tag == "!!float") {
			var decoded interface{}
			if err := node.Decode(&decoded); err == nil {
				return decoded, nil
			}
		}
		return value, nil
	default:
		return nil, nil
	}
}

// indexSeqPositions indexes block mapping items within a sequence. Route each
// item through the ordinary mapping indexer so the item mapping itself gets a
// mapInfo insertion anchor in addition to its existing scalar and descendant
// indexes.
func indexSeqPositions(st *docState, seq *yaml.Node, cur []string) {
	if seq == nil || seq.Kind != yaml.SequenceNode || seq.Style&yaml.FlowStyle != 0 {
		return
	}
	for idx, it := range seq.Content {
		if it == nil || it.Kind != yaml.MappingNode {
			continue
		}
		itemPath := append(append([]string(nil), cur...), indexSeg(idx))
		indexPositions(st, it, itemPath)
	}
}

// indexScalarSeqPositions indexes positions for sequence items which are scalar nodes.
func indexScalarSeqPositions(st *docState, seq *yaml.Node, cur []string) {
	if seq == nil || seq.Kind != yaml.SequenceNode || seq.Style&yaml.FlowStyle != 0 {
		return
	}

	// Optimization/Safety: Only process if it appears to be primarily a sequence of scalars.
	// Mixed sequences (scalars and mappings) are complex; we prioritize mapping indexing.
	isScalarSeq := true
	for _, it := range seq.Content {
		if it != nil && it.Kind != yaml.ScalarNode {
			// If we find a non-scalar, we rely on indexSeqPositions (for mappings)
			// or indexSequenceAnchors (for structure) but skip scalar indexing here
			// to avoid conflicts if structure is complex.
			isScalarSeq = false
			break
		}
	}
	if !isScalarSeq {
		return
	}

	for idx, it := range seq.Content {
		if it == nil {
			continue
		}

		// We have a scalar item. Index its value position.
		valStart := scalarValueOffset(st.original, st.lineOffsets, it)
		if valStart < 0 || valStart >= len(st.original) {
			continue
		}
		valEnd := findScalarEndOnLine(st.original, valStart)
		lineEnd := findLineEnd(st.original, valStart)

		// Include the sequence index in the length-prefixed internal path key.
		pk := makeSeqItemPathKey(cur, idx)
		st.valueOccByPathKey[pk] = append(st.valueOccByPathKey[pk], valueOcc{
			keyLineStart: lineStartOffset(st.lineOffsets, it.Line),
			valStart:     valStart,
			valEnd:       valEnd,
			lineEnd:      lineEnd,
			tag:          it.Tag,
			explicitTag:  scalarHasExplicitTag(st.original, st.lineOffsets, it),
			blockStyle:   it.Style&(yaml.LiteralStyle|yaml.FoldedStyle) != 0,
			multiline:    scalarSpansPhysicalLines(st.original, it, valStart, leadingSpaces(st.original[lineStartOffset(st.lineOffsets, it.Line):min(findLineEnd(st.original, valStart)+1, len(st.original))])),
		})
	}
}

// indexSequenceAnchors captures indent/style and insertion anchors for sequences (both scalars and mappings).
func indexSequenceAnchors(st *docState, seq *yaml.Node, cur []string) {
	if seq == nil || seq.Style&yaml.FlowStyle != 0 {
		return
	}
	mpath := joinPath(cur)
	si := st.seqIndex[mpath]
	if si == nil {
		si = &seqInfo{originalPath: true}
		st.seqIndex[mpath] = si
	}
	if len(seq.Content) == 0 {
		si.hasAnyItem = false
		si.items = nil
		si.gaps = nil
		return
	}
	si.hasAnyItem = true

	// Per‑item boundaries and identities (name or scalar value)
	si.items = si.items[:0]

	// Detect style/indent/key order from the FIRST item we see (for stability).
	detectedStyle := false

	computeItemBounds := func(it *yaml.Node) (start int, end int, name string) {
		if it == nil {
			return
		}
		// start (beginning of the first line of the item)
		if it.Kind == yaml.MappingNode && len(it.Content) >= 2 {
			fk := it.Content[0]
			start = lineStartOffset(st.lineOffsets, fk.Line)
			// yaml.v3 locates a block mapping at its first key, not at a
			// preceding standalone sequence dash/property line:
			//
			//   - &anchor
			//     key: value
			//
			// A whole-item/sequence replacement must include that line or it
			// leaves an orphan dash behind. Pull the start back one physical line
			// when the previous line can only be the introducer for this node.
			if start > 0 {
				prevEnd := start - 1
				if prevEnd > 0 && st.original[prevEnd] == '\n' {
					prevEnd--
				}
				prevStart := prevEnd
				for prevStart > 0 && st.original[prevStart-1] != '\n' {
					prevStart--
				}
				prevLine := bytes.TrimSpace(st.original[prevStart : prevEnd+1])
				if len(prevLine) > 0 && prevLine[0] == '-' {
					rest := bytes.TrimSpace(prevLine[1:])
					if len(rest) == 0 || rest[0] == '#' || rest[0] == '&' || rest[0] == '!' {
						start = prevStart
					}
				}
			}
		} else {
			start = lineStartOffset(st.lineOffsets, it.Line)
		}

		// end (newline ending the last line of the item)
		if it.Kind == yaml.MappingNode {
			maxEnd := 0
			for j := 0; j+1 < len(it.Content); j += 2 {
				v := it.Content[j+1]
				if v == nil {
					continue
				}
				le := maxLineEndForNode(st, v)
				if le > maxEnd {
					maxEnd = le
				}
			}
			if maxEnd == 0 {
				end = findLineEnd(st.original, start)
			} else {
				end = maxEnd
			}
		} else {
			end = maxLineEndForNode(st, it)
			if end == 0 {
				end = findLineEnd(st.original, start)
			}
		}
		// Node positions identify token starts, not general token ends. Extend an
		// item through quoted scalars and flow collections that close on a later
		// line so a whole-sequence rewrite cannot leave continuation bytes behind.
		if delimitedEnd := sourceDelimitedSubtreeEnd(st.original, st.lineOffsets, it); delimitedEnd > 0 {
			lastTokenByte := min(delimitedEnd-1, len(st.original)-1)
			if tokenLineEnd := findLineEnd(st.original, lastTokenByte); tokenLineEnd > end {
				end = tokenLineEnd
			}
		}

		// name (best-effort identity: "name" field value or scalar value)
		if it.Kind == yaml.MappingNode {
			for j := 0; j+1 < len(it.Content); j += 2 {
				k := it.Content[j]
				v := it.Content[j+1]
				if isStringMappingKey(k, "name") && v.Kind == yaml.ScalarNode {
					name = v.Value
					break
				}
			}
		} else if it.Kind == yaml.ScalarNode {
			name = it.Value
		}

		if !detectedStyle {
			le := findLineEnd(st.original, start)
			if start < 0 || start >= len(st.original) {
				return
			}
			lnEnd := le
			if le < len(st.original) && st.original[le] == '\n' {
			} else if le == len(st.original)-1 {
				lnEnd = len(st.original)
			}
			if start >= lnEnd {
				return
			}
			ln := st.original[start:lnEnd]
			si.indent = leadingSpaces(ln)
			si.firstKeyInline = firstNonSpaceByte(ln) == '-'

			if it.Kind == yaml.MappingNode && len(it.Content) >= 2 {
				kvIndent := 0
				for j := 0; j+1 < len(it.Content); j += 2 {
					k := it.Content[j]
					ks := lineStartOffset(st.lineOffsets, k.Line)
					ke := findLineEnd(st.original, ks)
					if ks < 0 || ks >= len(st.original) {
						continue
					}
					klEnd := ke
					if ke < len(st.original) && st.original[ke] == '\n' {
					} else if ke == len(st.original)-1 {
						klEnd = len(st.original)
					}
					if ks >= klEnd {
						continue
					}
					kl := st.original[ks:klEnd]
					if firstNonSpaceByte(kl) == '-' {
						continue
					}
					sp := leadingSpaces(kl)
					if kvIndent == 0 || (sp > 0 && sp < kvIndent) {
						kvIndent = sp
					}
				}

				if kvIndent == 0 {
					kvIndent = si.indent + st.indent
				}
				si.itemKVIndent = kvIndent

				order := make([]string, 0, len(it.Content)/2)
				for j := 0; j+1 < len(it.Content); j += 2 {
					if it.Content[j].Kind == yaml.ScalarNode {
						order = append(order, it.Content[j].Value)
					}
				}
				si.keyOrder = order
			} else {
				si.itemKVIndent = si.indent + st.indent
				si.keyOrder = nil
			}
			detectedStyle = true
		}
		return
	}

	first := seq.Content[0]
	if first == nil {
		return
	}

	fs, fe, nm := computeItemBounds(first)
	si.firstItemStart = fs

	lastEnd := fe
	si.items = make([]seqItemInfo, 0, len(seq.Content))
	si.items = append(si.items, seqItemInfo{name: nm, start: fs, end: fe})

	for _, it := range seq.Content[1:] {
		s, e, nm2 := computeItemBounds(it)
		if e > lastEnd {
			lastEnd = e
		}
		si.items = append(si.items, seqItemInfo{name: nm2, start: s, end: e})
	}
	si.lastItemEnd = lastEnd

	if len(si.items) >= 2 {
		si.gaps = make([][]byte, len(si.items)-1)
		for i := 0; i < len(si.items)-1; i++ {
			gStart := si.items[i].end + 1
			gEnd := si.items[i+1].start
			if gStart >= 0 && gEnd >= gStart && gEnd <= len(st.original) {
				si.gaps[i] = append([]byte(nil), st.original[gStart:gEnd]...)
			} else {
				si.gaps[i] = nil
			}
		}
	} else {
		si.gaps = nil
	}
}

func indexMappingHandles(st *docState, n *yaml.Node, cur []string) {
	if n == nil || n.Kind != yaml.MappingNode {
		return
	}
	st.subPathByHN[weak.Make(n)] = append([]string(nil), cur...)
	for i := 0; i+1 < len(n.Content); i += 2 {
		k := n.Content[i]
		v := n.Content[i+1]
		if k.Kind == yaml.ScalarNode && k.Tag == "!!str" {
			seg := k.Value
			if v.Kind == yaml.MappingNode {
				indexMappingHandles(st, v, append(cur, seg))
			}
		}
	}
}

// indexPositions populates indices for surgical edits: mapIndex, valueOccByPathKey, seqIndex, and boundsByPathKey.
func indexPositions(st *docState, n *yaml.Node, cur []string) {
	if n == nil || n.Kind != yaml.MappingNode || n.Style&yaml.FlowStyle != 0 {
		return
	}
	mapPath := joinPath(cur)
	mi := st.mapIndex[mapPath]
	if mi == nil {
		mi = &mapInfo{indent: 0, lastLineEnd: 0, hasAnyKey: false, originalPath: true}
		st.mapIndex[mapPath] = mi
	}

	for i := 0; i+1 < len(n.Content); i += 2 {
		k := n.Content[i]
		v := n.Content[i+1]
		if k.Kind != yaml.ScalarNode {
			continue
		}
		key := k.Value
		pk := makePathKey(cur, key)

		if k.Column > 0 && mi.indent == 0 && !(len(cur) == 0 && k.Column-1 == 0) {
			mi.indent = k.Column - 1
		}
		if len(cur) == 0 {
			mi.indent = 0
		}

		keyLineStart := lineStartOffset(st.lineOffsets, k.Line)
		valStart := scalarValueOffset(st.original, st.lineOffsets, v)

		var lineEnd int
		if valStart >= 0 && valStart < len(st.original) {
			lineEnd = findLineEnd(st.original, valStart)
			mi.hasAnyKey = true
		} else {
			lineEnd = findLineEnd(st.original, keyLineStart)
			mi.hasAnyKey = true
		}

		if v.Kind == yaml.ScalarNode && valStart >= 0 && valStart < len(st.original) {
			if valStart < len(st.original) {
				ch := st.original[valStart]
				if ch == '|' || ch == '>' {
					keyIndent := 0
					if k.Column > 0 {
						keyIndent = k.Column - 1
					}
					lineEnd = extendScalarBlockEnd(st.original, st.lineOffsets, v.Line, keyIndent)
				}
			}
		}

		// yaml.v3 positions identify token starts, not their complete lexical
		// extent. A mapping insertion is anchored after the last original value,
		// so extend that anchor through multiline quoted scalars and flow
		// collections even when their continuation closes at a lower indentation.
		if lexicalEnd := sourceDelimitedSubtreeEnd(st.original, st.lineOffsets, v); lexicalEnd > 0 {
			lastTokenByte := min(lexicalEnd-1, len(st.original)-1)
			if tokenLineEnd := findLineEnd(st.original, lastTokenByte); tokenLineEnd > lineEnd {
				lineEnd = tokenLineEnd
			}
		}
		// Plain scalars have no closing delimiter. Extend them only through
		// physical continuation lines more indented than their owning key. Using
		// maxLineEndForNode here would infer the sequence-item indentation and may
		// overrun a later field in an inline `- key: value` mapping.
		if v.Kind == yaml.ScalarNode && v.Style == 0 && valStart >= 0 && valStart < len(st.original) &&
			scalarSpansPhysicalLines(st.original, v, valStart, k.Column-1) {
			if scalarLineEnd := extendScalarBlockEnd(st.original, st.lineOffsets, v.Line, k.Column-1); scalarLineEnd > lineEnd {
				lineEnd = scalarLineEnd
			}
		}

		if v.Kind == yaml.MappingNode {
			childPath := append(cur, key)
			indexPositions(st, v, childPath)
			if childMi := st.mapIndex[joinPath(childPath)]; childMi != nil && childMi.lastLineEnd > lineEnd {
				lineEnd = childMi.lastLineEnd
			}
		} else if v.Kind == yaml.SequenceNode {
			seqPath := append(cur, key)
			indexSeqPositions(st, v, seqPath)
			indexScalarSeqPositions(st, v, seqPath)
			indexSequenceAnchors(st, v, seqPath)
			if seqInfo := st.seqIndex[joinPath(seqPath)]; seqInfo != nil && seqInfo.lastItemEnd > lineEnd {
				lineEnd = seqInfo.lastItemEnd
			}
		}

		if v.Kind == yaml.ScalarNode && valStart >= 0 && valStart < len(st.original) {
			valEnd := findScalarEndOnLine(st.original, valStart)
			scalarLineEnd := findLineEnd(st.original, valStart)

			st.valueOccByPathKey[pk] = append(st.valueOccByPathKey[pk], valueOcc{
				keyLineStart: keyLineStart,
				valStart:     valStart,
				valEnd:       valEnd,
				lineEnd:      scalarLineEnd,
				tag:          v.Tag,
				explicitTag:  scalarHasExplicitTag(st.original, st.lineOffsets, v),
				blockStyle:   v.Style&(yaml.LiteralStyle|yaml.FoldedStyle) != 0,
				multiline:    scalarSpansPhysicalLines(st.original, v, valStart, k.Column-1),
			})
		}

		blockEnd := lineEnd
		if blockEnd >= 0 {
			if blockEnd < len(st.original) && st.original[blockEnd] == '\n' {
				blockEnd++
			} else if blockEnd == len(st.original)-1 {
				blockEnd = len(st.original)
			}
		}

		if keyLineStart >= 0 && keyLineStart <= len(st.original) && blockEnd >= keyLineStart && blockEnd <= len(st.original) {
			st.boundsByPathKey[pk] = append(st.boundsByPathKey[pk], kvBounds{
				start: keyLineStart,
				end:   blockEnd,
			})
		}

		if lineEnd > mi.lastLineEnd {
			mi.lastLineEnd = lineEnd
		}
	}
}
