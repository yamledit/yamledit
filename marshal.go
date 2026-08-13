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

// Marshal serializes a mapping document. Mutations made through yamledit APIs
// are emitted with byte surgery or scoped rewrites; if neither is safe, Marshal
// returns an error rather than globally reformatting the source. Direct changes
// to fields on the returned yaml.Node bypass the edit index, so Marshal encodes
// the live AST globally to honor them and may reflow unrelated formatting.
func Marshal(doc *yaml.Node) ([]byte, error) {
	st, ok := lookup(doc)
	if !ok {
		// Standalone caller-constructed nodes do not have Parse's structural
		// guarantees. Validate before invoking yaml.v3: its encoder otherwise
		// ignores an unmatched mapping child and panics on nil children.
		if err := validateYAMLMarshalDocument(doc); err != nil {
			return nil, err
		}
		out, err := standardEncode(doc, 2)
		if err != nil {
			return nil, err
		}
		return validateEditedOutput(out)
	}

	st.mu.RLock()
	// A caller may mutate the returned AST directly. Revalidate the complete
	// serializable graph while it is locked before indexing or encoding it.
	if err := validateYAMLMarshalDocument(doc); err != nil {
		st.mu.RUnlock()
		return nil, err
	}
	if err := validateOrderedUTF8(st.ordered); err != nil {
		st.mu.RUnlock()
		return nil, err
	}
	// The ordered shadow drives byte-diff selection, but the live AST is the
	// semantic authority. In particular, its Alias nodes resolve through the
	// current anchor target while the deliberately detached ordered shadow keeps
	// each alias expansion independent. Snapshot the live meaning while holding
	// the document lock and use it to verify every generated patch below.
	liveValue, err := yamlNodeToOrderedValue(doc.Content[0])
	if err != nil {
		st.mu.RUnlock()
		return nil, fmt.Errorf("yamledit: cannot snapshot live YAML semantics: %w", err)
	}
	semanticExpected, ok := liveValue.(gyaml.MapSlice)
	if !ok {
		st.mu.RUnlock()
		return nil, fmt.Errorf("yamledit: live document root is not a mapping")
	}
	if err := validateOrderedUTF8(semanticExpected); err != nil {
		st.mu.RUnlock()
		return nil, err
	}
	// Public mutators update expectedAST while holding this same state lock. A
	// mismatch therefore means the caller changed the returned yaml.Node tree
	// directly. Compare the graph and presentation, not only projected values:
	// tags, styles, comments, anchors, alias targets, duplicate keys, and complex
	// keys are all observable YAML state that an ordered-map shadow cannot carry.
	directASTMutation := st.directASTDirty || !yamlNodeGraphEqual(doc, st.expectedAST)
	marshalOrdered := st.ordered
	if len(st.original) == 0 {
		// Encode the live AST while holding the read lock. Snapshotting is not
		// sufficient for a new document because the encoder traverses doc itself.
		out, err := standardEncode(doc, st.indent)
		st.mu.RUnlock()
		if err != nil {
			return nil, err
		}
		return validateEditedOutput(out, semanticExpected)
	}
	if st.originalTriviaOnly {
		if !directASTMutation && logicalEqualOrdered(st.origOrdered, marshalOrdered) {
			out := append([]byte(nil), st.original...)
			st.mu.RUnlock()
			// A trivia-only source intentionally represents the package's
			// synthetic empty mapping even though a YAML decoder reports EOF.
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
		return validateEditedOutput(out, semanticExpected)
	}
	// A direct edit must be encoded from the live AST before any source-surgical
	// shortcut. This also preserves custom tags/anchors inserted into `{}` and
	// presentation-only edits whose projected value did not change.
	if directASTMutation {
		out, err := standardEncode(doc, st.indent)
		st.mu.RUnlock()
		if err != nil {
			return nil, err
		}
		return validateEditedOutput(out, semanticExpected)
	}
	if st.originalRootEmpty {
		// An explicit `{}` root has no stable key-line anchor for surgery. Keep
		// the exact input for a net-zero edit; otherwise encode the live AST while
		// it is protected by the state lock.
		if logicalEqualOrdered(st.origOrdered, marshalOrdered) {
			out := append([]byte(nil), st.original...)
			st.mu.RUnlock()
			return validateEditedOutput(out, semanticExpected)
		}
		if st.rootTokenEnd <= st.rootTokenStart || st.rootTokenEnd > len(st.original) {
			st.mu.RUnlock()
			return nil, fmt.Errorf("yamledit: cannot safely replace explicit empty root mapping")
		}
		rootValue := orderedToYAMLNode(cloneMapSlice(marshalOrdered))
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
		return validateEditedOutput(out, semanticExpected)
	}
	ordered := cloneMapSlice(marshalOrdered) // snapshot
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
	liveRootSnapshot := cloneYAMLNodeGraph(doc.Content[0])
	delSet := make(map[string]struct{}, len(st.toDelete))
	forceScalarRewrite := make(map[string]struct{}, len(st.forceScalarRewrite))
	nodeRewriteTargets := activeNodeRewriteIntentsLocked(st, doc.Content[0])
	seqIdx := cloneSeqIndex(st.seqIndex)
	for k := range st.toDelete {
		delSet[k] = struct{}{}
	}
	for path := range st.forceScalarRewrite {
		segments, ok := splitJoinedPath(path)
		if !ok {
			continue
		}
		value, exists := orderedValueAtSegments(st.ordered, segments)
		tag, scalar := scalarYAMLTag(value)
		if exists && scalar && tag == st.forceScalarTags[path] {
			forceScalarRewrite[path] = struct{}{}
			// Forced scalar tags are output invariants, not merely renderer
			// hints. This is especially important for scalar items in mixed
			// sequences, which intentionally have no byte-token index: an
			// unchanged surgical candidate must be rejected if it retains the
			// original custom tag.
			nodeRewriteTargets[path] = yamlNodeSignature{kind: yaml.ScalarNode, tag: tag, exists: true}
		}
	}
	for path := range nodeRewriteTargets {
		forceScalarRewrite[path] = struct{}{}
	}
	rootMappingEmpty := doc != nil && doc.Kind == yaml.DocumentNode && len(doc.Content) > 0 && doc.Content[0].Kind == yaml.MappingNode && len(doc.Content[0].Content) == 0
	st.mu.RUnlock()

	out, okPatch := marshalBySurgery(original, ordered, origOrdered, mapIdx, valIdx, seqIdx, boundsIdx, unsafePaths, semanticOpaquePaths, presentationOpaquePaths, indent, delSet, forceScalarRewrite)
	var surgicalValidationErr error
	if okPatch {
		validated, err := validateEditedOutputWithNodeIntents(out, nodeRewriteTargets, semanticExpected)
		if err == nil {
			return validated, nil
		}
		// A conservative byte patch can still prove incomplete when several
		// mutations interact. Do not let a historical "structural dirty" bit
		// decide forever whether surgery is usable; validate the actual candidate
		// and, when it fails, give the scoped structural renderer a chance.
		surgicalValidationErr = err
	}

	if patched, ok := structuralRewrite(original, ordered, origOrdered, liveRootSnapshot, boundsIdx, unsafePaths, opaquePaths, indent, delSet, forceScalarRewrite, nodeRewriteTargets, rootMappingEmpty); ok {
		return validateEditedOutputWithNodeIntents(patched, nodeRewriteTargets, semanticExpected)
	}
	if surgicalValidationErr != nil {
		return nil, surgicalValidationErr
	}

	return nil, fmt.Errorf("yamledit: surgical edit unsupported; no safe structural rewrite")
}

func validateEditedOutput(out []byte, expected ...gyaml.MapSlice) ([]byte, error) {
	return validateEditedOutputWithNodeIntents(out, nil, expected...)
}

func validateEditedOutputWithNodeIntents(out []byte, intents map[string]yamlNodeSignature, expected ...gyaml.MapSlice) ([]byte, error) {
	var doc yaml.Node
	if err := decodeSingleYAMLDocument(out, &doc); err != nil {
		return nil, fmt.Errorf("yamledit: edit would produce invalid YAML: %w", err)
	}
	if doc.Kind != yaml.DocumentNode || len(doc.Content) == 0 || doc.Content[0].Kind != yaml.MappingNode {
		return nil, fmt.Errorf("yamledit: edit would change the document root from a mapping")
	}
	if len(expected) > 0 {
		actual, err := yamlNodeToOrderedValue(doc.Content[0])
		if err != nil {
			return nil, fmt.Errorf("yamledit: cannot verify edited YAML semantics: %w", err)
		}
		actualMap, ok := actual.(gyaml.MapSlice)
		if !ok || !logicalEqualOrdered(expected[0], actualMap) {
			return nil, fmt.Errorf("yamledit: edit would not preserve the requested YAML values and types")
		}
	}
	for encoded, want := range intents {
		segments, ok := splitJoinedPath(encoded)
		if !ok {
			return nil, fmt.Errorf("yamledit: cannot verify requested YAML tag at an invalid internal path")
		}
		actual, exists := yamlNodeAtPathSegments(doc.Content[0], segments)
		if !exists || !sameYAMLNodeSignature(signatureOfYAMLNode(actual), want) {
			got := signatureOfYAMLNode(actual)
			return nil, fmt.Errorf("yamledit: edit would not preserve the requested YAML kind/tag at path %q (want kind %d tag %q, got kind %d tag %q)", strings.Join(segments, "/"), want.kind, want.tag, got.kind, got.tag)
		}
	}
	return out, nil
}

// yamlNodeGraphEqual compares the complete serializable YAML graph. Source
// positions are intentionally excluded: edits do not need to preserve parser
// coordinates, while every presentation field and alias edge is significant.
func yamlNodeGraphEqual(a, b *yaml.Node) bool {
	type nodePair struct {
		a *yaml.Node
		b *yaml.Node
	}
	seen := make(map[nodePair]struct{})
	var equal func(*yaml.Node, *yaml.Node) bool
	equal = func(left, right *yaml.Node) bool {
		if left == nil || right == nil {
			return left == right
		}
		pair := nodePair{a: left, b: right}
		if _, ok := seen[pair]; ok {
			return true
		}
		seen[pair] = struct{}{}
		if left.Kind != right.Kind || left.Style != right.Style || left.Tag != right.Tag ||
			left.Value != right.Value || left.Anchor != right.Anchor ||
			left.HeadComment != right.HeadComment || left.LineComment != right.LineComment ||
			left.FootComment != right.FootComment || len(left.Content) != len(right.Content) {
			return false
		}
		if (left.Alias == nil) != (right.Alias == nil) {
			return false
		}
		if left.Alias != nil && !equal(left.Alias, right.Alias) {
			return false
		}
		for i := range left.Content {
			if !equal(left.Content[i], right.Content[i]) {
				return false
			}
		}
		return true
	}
	return equal(a, b)
}

// standardEncode performs a standard YAML encoding without surgical editing.
// It is used for new documents and direct yaml.Node mutations; package-managed
// edits do not fall back globally when scoped editing is unsafe.
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
func structuralRewrite(original []byte, ordered gyaml.MapSlice, origOrdered gyaml.MapSlice, liveRoot *yaml.Node, boundsIdx map[string][]kvBounds, unsafePaths, opaquePaths map[string]struct{}, baseIndent int, delSet, forceScalarRewrite map[string]struct{}, nodeRewriteTargets map[string]yamlNodeSignature, rootMappingEmpty bool) ([]byte, bool) {
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
	for pk := range forceScalarRewrite {
		changed = append(changed, pk)
	}
	// A sequence item has no independent mapping-entry byte range. When an exact
	// tag replacement occurs there, render the nearest bounded ancestor from the
	// final live AST. This retains all untouched YAML-only metadata in that scoped
	// subtree, unlike the ordered JSON-shaped shadow.
	liveRewritePaths := make(map[string]struct{})
	for encoded := range nodeRewriteTargets {
		segments, ok := splitJoinedPath(encoded)
		if !ok {
			return nil, false
		}
		for depth := len(segments); depth >= 1; depth-- {
			ancestor := joinPath(segments[:depth])
			if len(boundsIdx[ancestor]) == 0 {
				continue
			}
			if depth == len(segments) {
				if _, unsafe := unsafePaths[ancestor]; !unsafe {
					if _, opaque := opaquePaths[ancestor]; !opaque {
						break
					}
				}
			}
			liveRewritePaths[ancestor] = struct{}{}
			changed = append(changed, ancestor)
			break
		}
	}
	findSafeContainerAncestor := func(pk string) (string, bool) {
		parts, ok := splitJoinedPath(pk)
		if !ok {
			return "", false
		}
		for i := len(parts) - 1; i >= 1; i-- {
			ancestor := joinPath(parts[:i])
			if _, live := liveRewritePaths[ancestor]; live {
				return ancestor, true
			}
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
	sort.SliceStable(changed, func(i, j int) bool {
		left, _ := splitJoinedPath(changed[i])
		right, _ := splitJoinedPath(changed[j])
		return len(left) < len(right)
	})
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

	// Scoped structural rewrite must honor last-wins duplicate semantics too.
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
		_, liveRewrite := liveRewritePaths[pk]
		if _, unsafe := unsafePaths[pk]; unsafe && !liveRewrite {
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
		if liveRewrite {
			b := bounds[len(bounds)-1]
			txt, ok := renderLiveMappingEntry(original, liveRoot, append(path, key), b, baseIndent)
			if !ok {
				return nil, false
			}
			if !bytes.Equal(original[b.start:b.end], []byte(txt)) {
				patches = append(patches, patch{start: b.start, end: b.end, data: []byte(txt)})
			}
			patched[pk] = struct{}{}
			rewritten[pk] = struct{}{}
			continue
		}
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
			var seqText string
			var okSeq bool
			if hasNodeRewriteTargetAtOrBelow(nodeRewriteTargets, append(path, key)) {
				seqText, okSeq = renderKeyValue(original, key, val, b, baseIndent, append(path, key), nodeRewriteTargets)
			} else {
				target, overrideTag := nodeRewriteTargets[pk]
				seqText, okSeq = renderSequenceValue(original, key, val, b, baseIndent, target, overrideTag)
			}
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

		txt, ok := renderKeyValue(original, key, val, b, baseIndent, append(path, key), nodeRewriteTargets)
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

func orderedValueAtSegments(ms gyaml.MapSlice, segments []string) (interface{}, bool) {
	var current interface{} = ms
	for _, segment := range segments {
		switch value := current.(type) {
		case gyaml.MapSlice:
			var found bool
			for i := len(value) - 1; i >= 0; i-- {
				if keyEquals(value[i].Key, segment) {
					current = value[i].Value
					found = true
					break
				}
			}
			if !found {
				return nil, false
			}
		case []interface{}:
			if !isIndexPathSegment(segment) {
				return nil, false
			}
			index, err := strconv.Atoi(segment[1 : len(segment)-1])
			if err != nil || index < 0 || index >= len(value) {
				return nil, false
			}
			current = value[index]
		default:
			return nil, false
		}
	}
	return current, true
}

func hasNodeRewriteTargetAtOrBelow(targets map[string]yamlNodeSignature, path []string) bool {
	for encoded := range targets {
		segments, ok := splitJoinedPath(encoded)
		if ok && len(segments) >= len(path) && pathSegmentsEqual(segments[:len(path)], path) {
			return true
		}
	}
	return false
}

func applyNodeRewriteTargets(valueNode *yaml.Node, valuePath []string, targets map[string]yamlNodeSignature) bool {
	for encoded, target := range targets {
		segments, ok := splitJoinedPath(encoded)
		if !ok || len(segments) < len(valuePath) || !pathSegmentsEqual(segments[:len(valuePath)], valuePath) {
			continue
		}
		node, exists := yamlNodeAtPathSegments(valueNode, segments[len(valuePath):])
		if !exists || node.Kind != target.kind {
			return false
		}
		node.Tag = target.tag
		if target.kind == yaml.ScalarNode && target.tag != "" {
			node.Style &^= yaml.TaggedStyle
		}
	}
	return true
}

func renderLiveMappingEntry(original []byte, liveRoot *yaml.Node, path []string, b kvBounds, baseIndent int) (string, bool) {
	if liveRoot == nil || len(path) == 0 {
		return "", false
	}
	parent, exists := yamlNodeAtPathSegments(liveRoot, path[:len(path)-1])
	if !exists || parent.Kind != yaml.MappingNode {
		return "", false
	}
	keyName := path[len(path)-1]
	var keyNode, valueNode *yaml.Node
	for index := len(parent.Content) - 2; index >= 0; index -= 2 {
		if isStringMappingKey(parent.Content[index], keyName) {
			keyNode, valueNode = parent.Content[index], parent.Content[index+1]
			break
		}
	}
	if keyNode == nil || valueNode == nil {
		return "", false
	}

	entry := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map", Content: []*yaml.Node{keyNode, valueNode}}
	entry = cloneYAMLNodeGraph(entry)
	doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{entry}}
	lines, ok := encodeNodeLines(doc, baseIndent)
	if !ok || len(lines) == 0 {
		return "", false
	}

	indentSpaces := currentIndent(original, b.start)
	inlineSequenceKey := false
	lineEnd := findLineEnd(original, b.start)
	if lineEnd >= b.start && b.start < len(original) {
		line := original[b.start:min(lineEnd+1, len(original))]
		first := leadingSpaces(line)
		inlineSequenceKey = first+1 < len(line) && line[first] == '-' && (line[first+1] == ' ' || line[first+1] == '\t')
	}
	for index := range lines {
		prefix := strings.Repeat(" ", indentSpaces)
		if inlineSequenceKey {
			if index == 0 {
				prefix += "- "
			} else {
				prefix = strings.Repeat(" ", indentSpaces+2)
			}
		}
		lines[index] = prefix + lines[index]
	}
	output := strings.Join(lines, "\n")
	if b.end > b.start && b.end <= len(original) && original[b.end-1] == '\n' {
		output += "\n"
	}
	return output, true
}

func renderKeyValue(original []byte, key string, val interface{}, b kvBounds, baseIndent int, valuePath []string, nodeRewriteTargets map[string]yamlNodeSignature) (string, bool) {
	// IMPORTANT: do NOT convert to map[string]interface{} (it loses key order).
	// Build a yaml.Node mapping and encode that (preserves gyaml.MapSlice order).
	root := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
	valueNode := orderedToYAMLNode(val)
	valueNode.Anchor = b.anchor
	if b.collectionTag != "" && (valueNode.Kind == yaml.MappingNode || valueNode.Kind == yaml.SequenceNode) {
		valueNode.Tag = b.collectionTag
	}
	if !applyNodeRewriteTargets(valueNode, valuePath, nodeRewriteTargets) {
		return "", false
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

func renderSequenceValue(original []byte, key string, val interface{}, b kvBounds, baseIndent int, target yamlNodeSignature, overrideTag bool) (string, bool) {
	arr, ok := val.([]interface{})
	if !ok {
		return "", false
	}
	indentSpaces := currentIndent(original, b.start)
	comment := inlineComment(original, b.start)

	var sb strings.Builder
	sb.WriteString(strings.Repeat(" ", indentSpaces))
	sb.WriteString(renderMappingKey(key))
	collectionTag := b.collectionTag
	if overrideTag && target.exists && target.kind == yaml.SequenceNode {
		if target.tag == "!!seq" {
			collectionTag = ""
		} else {
			collectionTag = target.tag
		}
	}
	if len(arr) == 0 {
		sb.WriteString(":")
		if collectionTag != "" {
			sb.WriteString(" ")
			sb.WriteString(renderYAMLTagProperty(collectionTag))
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
	if collectionTag != "" {
		sb.WriteString(" ")
		sb.WriteString(renderYAMLTagProperty(collectionTag))
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
