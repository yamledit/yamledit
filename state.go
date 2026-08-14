package yamledit

import (
	"runtime"
	"strconv"
	"sync"
	"weak"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// Internal state registered per root yaml.DocumentNode.
type docState struct {
	mu  sync.RWMutex
	doc weak.Pointer[yaml.Node] // weak reference to the root document
	// expectedAST is a graph-preserving snapshot of the live tree after the last
	// state-aware library mutation. Marshal compares it with the public yaml.Node
	// tree to detect direct caller edits, including presentation-only changes that
	// cannot be represented in the ordered logical shadow.
	expectedAST *yaml.Node
	// originalAST is an immutable graph snapshot of the parsed source tree.
	// Node-rewrite intents are compared with the node originally occupying their
	// final path, which remains correct when sequence insertions rebase an edit.
	originalAST *yaml.Node
	// directASTDirty remains set if a public mutator observes that the caller had
	// already changed the live tree. A later library snapshot must not bless and
	// then silently discard that earlier direct presentation edit.
	directASTDirty bool
	indent         int                                  // detected indent (2,3,4,...)
	indentSeq      bool                                 // whether sequences under a key are indented
	ordered        gyaml.MapSlice                       // current ordered mapping we edit (live view)
	comments       gyaml.CommentMap                     // captured comments (for fallback encode)
	subPathByHN    map[weak.Pointer[yaml.Node]][]string // weak mapping-handle -> path segments

	// --- Byte-surgical indices ---
	original []byte // original file bytes (exact)
	// originalRootEmpty records a non-empty source document whose root was an
	// explicit empty mapping (for example "{}"). Such a document has no byte
	// insertion anchor, so the first real edit must use the standard encoder.
	originalRootEmpty  bool
	originalTriviaOnly bool
	rootTokenStart     int
	rootTokenEnd       int
	lineOffsets        []int // starting offset of each line in original
	origOrdered        gyaml.MapSlice

	// Map-level index: information about each mapping path found in the original bytes
	mapIndex map[string]*mapInfo

	// Scalar value positions (original) keyed by path + key (we store all occurrences to handle dups)
	// Also stores scalar sequence items keyed by path + [index].
	valueOccByPathKey map[string][]valueOcc

	// Key-Value boundaries for all types (scalar, mapping, sequence) for surgical deletion.
	boundsByPathKey map[string][]kvBounds
	unsafePathKeys  map[string]struct{}
	opaquePathKeys  map[string]struct{} // container rewrites would lose source-only metadata

	seqIndex map[string]*seqInfo // sequence formatting & anchors by YAML path
	// forceScalarRewrite records scalar paths whose requested YAML tag changed
	// even though their projected Go value did not (for example timestamp to
	// string with the same spelling).
	forceScalarRewrite map[string]struct{}
	// forceScalarTags stores the requested target tag for each forced rewrite.
	// A later operation at the same path can then cancel or replace stale intent.
	forceScalarTags map[string]string
	// nodeRewriteIntents records the YAML kind/tag at a path before the first
	// state-aware replacement and the kind/tag most recently requested there.
	// The ordered logical shadow deliberately omits YAML tags, so a replacement
	// can otherwise appear to be a no-op and Marshal may return the original tag.
	// Keeping the origin across several operations also handles delete/re-add and
	// complex-to-scalar round trips without treating edits inside a tagged
	// collection as a replacement of that collection itself.
	nodeRewriteIntents map[string]nodeRewriteIntent

	// explicit deletions requested (path\0key)
	toDelete map[string]struct{}
}

type yamlNodeSignature struct {
	kind   yaml.Kind
	tag    string
	exists bool
}

type nodeRewriteIntent struct {
	origin                     yamlNodeSignature
	target                     yamlNodeSignature
	removedDuringEdits         bool
	wholeCollectionReplacement bool
}

func signatureOfYAMLNode(node *yaml.Node) yamlNodeSignature {
	if node == nil {
		return yamlNodeSignature{}
	}
	return yamlNodeSignature{kind: node.Kind, tag: node.Tag, exists: true}
}

func sameYAMLNodeSignature(left, right yamlNodeSignature) bool {
	return left.exists == right.exists && (!left.exists || left.kind == right.kind && left.tag == right.tag)
}

// recordNodeReplacementIntentLocked records an exact-path replacement. old is
// the node visible before the replacement and target is the requested output
// kind/tag. An existing origin is retained so a sequence such as
// custom-scalar -> mapping -> string is compared with the original custom tag,
// not merely with the intermediate mapping.
func recordNodeReplacementIntentLocked(st *docState, path []string, old *yaml.Node, target yamlNodeSignature) {
	if st == nil || len(path) == 0 || !target.exists {
		return
	}
	if st.nodeRewriteIntents == nil {
		st.nodeRewriteIntents = make(map[string]nodeRewriteIntent)
	}
	encoded := joinPath(path)
	intent, seen := st.nodeRewriteIntents[encoded]
	if !seen {
		intent.origin = signatureOfYAMLNode(old)
	}
	intent.target = target
	// Ordinary replacements preserve any source presentation that remains
	// compatible with the requested kind/tag. Whole collection replacement opts
	// into a whole-value rewrite separately.
	intent.wholeCollectionReplacement = false
	st.nodeRewriteIntents[encoded] = intent

	// Replacing a container also replaces every descendant. Preserve each
	// descendant's origin for a possible later recreation, but do not enforce a
	// stale target while that old subtree is absent.
	for descendant, childIntent := range st.nodeRewriteIntents {
		if descendant == encoded {
			continue
		}
		segments, ok := splitJoinedPath(descendant)
		if ok && len(segments) > len(path) && pathSegmentsEqual(segments[:len(path)], path) {
			childIntent.target = yamlNodeSignature{}
			st.nodeRewriteIntents[descendant] = childIntent
		}
	}
}

// markWholeCollectionReplacementIntentLocked records that a complete mapping
// or sequence was replaced rather than edited descendant-by-descendant. The
// replacement is therefore authoritative even when source and target have the
// same YAML kind and tag (for example SetValue with SortKeys).
func markWholeCollectionReplacementIntentLocked(st *docState, path []string) {
	if st == nil || len(path) == 0 {
		return
	}
	encoded := joinPath(path)
	intent, ok := st.nodeRewriteIntents[encoded]
	if !ok || !intent.target.exists ||
		(intent.target.kind != yaml.MappingNode && intent.target.kind != yaml.SequenceNode) {
		return
	}
	intent.wholeCollectionReplacement = true
	st.nodeRewriteIntents[encoded] = intent
}

func recordNodeRemovalIntentLocked(st *docState, path []string, old *yaml.Node) {
	if st == nil || len(path) == 0 {
		return
	}
	if st.nodeRewriteIntents == nil {
		st.nodeRewriteIntents = make(map[string]nodeRewriteIntent)
	}
	encoded := joinPath(path)
	intent, seen := st.nodeRewriteIntents[encoded]
	if !seen {
		intent.origin = signatureOfYAMLNode(old)
	}
	intent.target = yamlNodeSignature{}
	intent.removedDuringEdits = true
	intent.wholeCollectionReplacement = false
	st.nodeRewriteIntents[encoded] = intent
	for descendant, childIntent := range st.nodeRewriteIntents {
		segments, ok := splitJoinedPath(descendant)
		if ok && len(segments) > len(path) && pathSegmentsEqual(segments[:len(path)], path) {
			childIntent.target = yamlNodeSignature{}
			st.nodeRewriteIntents[descendant] = childIntent
		}
	}
}

// recordShiftedSubtreeIntentsLocked snapshots the kind/tag signatures now
// occupying a sequence index after an insertion or removal. Logical sequence
// values do not carry custom YAML tags, and every later item can shift across a
// source position with different metadata even when all values compare equal.
// Record the full addressable subtree against the immutable source paths so
// Marshal validates (and, if needed, rewrites) every such difference.
func recordShiftedSubtreeIntentsLocked(st *docState, path []string, shifted *yaml.Node) {
	if st == nil || len(path) == 0 || shifted == nil {
		return
	}
	if st.nodeRewriteIntents == nil {
		st.nodeRewriteIntents = make(map[string]nodeRewriteIntent)
	}
	originalRoot := st.originalAST
	if originalRoot != nil && originalRoot.Kind == yaml.DocumentNode && len(originalRoot.Content) == 1 {
		originalRoot = originalRoot.Content[0]
	}

	var walk func(*yaml.Node, []string)
	walk = func(current *yaml.Node, currentPath []string) {
		if current == nil {
			return
		}
		original, exists := yamlNodeAtPathSegments(originalRoot, currentPath)
		encoded := joinPath(currentPath)
		if exists {
			intent := nodeRewriteIntent{
				origin: signatureOfYAMLNode(original),
				target: signatureOfYAMLNode(current),
			}
			if previous, ok := st.nodeRewriteIntents[encoded]; ok {
				intent.removedDuringEdits = previous.removedDuringEdits
				intent.wholeCollectionReplacement = previous.wholeCollectionReplacement
			}
			st.nodeRewriteIntents[encoded] = intent
		} else {
			// No source node occupies this final path (for example an append beyond
			// the original sequence length). Ordinary rebased history belongs to a
			// different item and must not constrain the new subtree. A mapping-entry
			// reinsertion marker is different: it follows the same live item and may
			// move back onto an original index after a transient insertion is removed.
			// Retain lifecycle/provenance that follows the same logical item and
			// refresh its live target while it is parked beyond the source sequence.
			if previous, ok := st.nodeRewriteIntents[encoded]; ok && previous.removedDuringEdits {
				previous.target = signatureOfYAMLNode(current)
				st.nodeRewriteIntents[encoded] = previous
			} else {
				delete(st.nodeRewriteIntents, encoded)
			}
		}
		switch current.Kind {
		case yaml.MappingNode:
			for index := 0; index+1 < len(current.Content); index += 2 {
				key, value := current.Content[index], current.Content[index+1]
				if key == nil || value == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
					continue
				}
				childPath := append(append([]string(nil), currentPath...), key.Value)
				walk(value, childPath)
			}
		case yaml.SequenceNode:
			for index, value := range current.Content {
				childPath := append(append([]string(nil), currentPath...), indexSeg(index))
				walk(value, childPath)
			}
		}
	}
	walk(shifted, path)
}

func yamlNodeAtPathSegments(root *yaml.Node, path []string) (*yaml.Node, bool) {
	current := root
	for _, segment := range path {
		if current == nil {
			return nil, false
		}
		switch current.Kind {
		case yaml.MappingNode:
			var child *yaml.Node
			for index := len(current.Content) - 2; index >= 0; index -= 2 {
				if isStringMappingKey(current.Content[index], segment) {
					child = current.Content[index+1]
					break
				}
			}
			if child == nil {
				return nil, false
			}
			current = child
		case yaml.SequenceNode:
			if !isIndexPathSegment(segment) {
				return nil, false
			}
			index, err := strconv.Atoi(segment[1 : len(segment)-1])
			if err != nil || index < 0 || index >= len(current.Content) {
				return nil, false
			}
			current = current.Content[index]
		default:
			return nil, false
		}
	}
	return current, current != nil
}

// activeNodeRewriteIntentsLocked returns only final, live replacements whose
// requested kind/tag differs from the node in the original source at that final
// path. Comparing at Marshal time is important for sequence insertions: an edit
// intent can move to another index, and its output must then be compared with
// the bytes originally occupying the rebased index.
// The caller must hold st.mu. Stale intents are ignored; a mismatch between the
// live node and the recorded target can only arise from a direct AST edit, which
// Marshal handles by encoding the live tree.
func activeNodeRewriteIntentsLocked(st *docState, root *yaml.Node) map[string]yamlNodeSignature {
	active := make(map[string]yamlNodeSignature)
	if st == nil || root == nil {
		return active
	}
	for encoded, intent := range st.nodeRewriteIntents {
		if !intent.target.exists {
			continue
		}
		path, ok := splitJoinedPath(encoded)
		if !ok {
			continue
		}
		current, exists := yamlNodeAtPathSegments(root, path)
		if !exists || !sameYAMLNodeSignature(signatureOfYAMLNode(current), intent.target) {
			continue
		}
		originalRoot := st.originalAST
		if originalRoot != nil && originalRoot.Kind == yaml.DocumentNode && len(originalRoot.Content) == 1 {
			originalRoot = originalRoot.Content[0]
		}
		original, existedOriginally := yamlNodeAtPathSegments(originalRoot, path)
		if !existedOriginally ||
			(sameYAMLNodeSignature(signatureOfYAMLNode(original), intent.target) && !intent.wholeCollectionReplacement) {
			continue
		}
		if !intent.origin.exists {
			// A genuinely new node at an index must not be compared with the old
			// occupant that was shifted away by insertion. An origin-less intent is
			// only a replacement when a preceding remove explicitly left a tombstone
			// for this exact path.
			continue
		}
		active[encoded] = intent.target
	}
	return active
}

// activeMappingReinsertionsLocked returns original mapping entries that were
// removed and later recreated. Their live AST position is authoritative: they
// are new keys for ordering purposes and must not be patched back into their
// old source slot. Sequence item removals are handled by sequence surgery, so
// only mapping-entry paths are collected here.
func activeMappingReinsertionsLocked(st *docState, root *yaml.Node) []string {
	if st == nil || root == nil {
		return nil
	}
	originalRoot := st.originalAST
	if originalRoot != nil && originalRoot.Kind == yaml.DocumentNode && len(originalRoot.Content) == 1 {
		originalRoot = originalRoot.Content[0]
	}
	marked := make(map[string]struct{})
	for encoded, intent := range st.nodeRewriteIntents {
		if !intent.removedDuringEdits || !intent.target.exists {
			continue
		}
		path, ok := splitJoinedPath(encoded)
		if !ok || len(path) == 0 || isIndexPathSegment(path[len(path)-1]) {
			continue
		}
		current, exists := yamlNodeAtPathSegments(root, path)
		if !exists || !sameYAMLNodeSignature(signatureOfYAMLNode(current), intent.target) {
			continue
		}
		if _, existedOriginally := yamlNodeAtPathSegments(originalRoot, path); !existedOriginally {
			continue
		}
		marked[encoded] = struct{}{}
	}
	if len(marked) == 0 {
		return nil
	}

	var ordered []string
	selected := make(map[string]struct{})
	var walk func(*yaml.Node, []string)
	walk = func(node *yaml.Node, path []string) {
		if node == nil {
			return
		}
		switch node.Kind {
		case yaml.MappingNode:
			for index := 0; index+1 < len(node.Content); index += 2 {
				key, value := node.Content[index], node.Content[index+1]
				if key == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
					continue
				}
				childPath := append(append([]string(nil), path...), key.Value)
				encoded := joinPath(childPath)
				if _, exists := marked[encoded]; exists {
					covered := false
					for depth := len(childPath) - 1; depth >= 1; depth-- {
						if _, ancestor := selected[joinPath(childPath[:depth])]; ancestor {
							covered = true
							break
						}
					}
					if !covered {
						ordered = append(ordered, encoded)
						selected[encoded] = struct{}{}
					}
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
	return ordered
}

// restoreRecreatedMappingEntryCommentsLocked keeps the package's comment
// preservation guarantee when a mapping key is removed and recreated before
// Marshal. The recreated value keeps its requested kind/tag/style; only comment
// fields attached to the original key and value nodes are restored.
func restoreRecreatedMappingEntryCommentsLocked(st *docState, path []string) {
	if st == nil || len(path) == 0 {
		return
	}
	liveRoot := st.root()
	if liveRoot == nil || liveRoot.Kind != yaml.DocumentNode || len(liveRoot.Content) != 1 {
		return
	}
	liveRoot = liveRoot.Content[0]
	originalRoot := st.originalAST
	if originalRoot == nil {
		return
	}
	if originalRoot.Kind == yaml.DocumentNode && len(originalRoot.Content) == 1 {
		originalRoot = originalRoot.Content[0]
	}
	liveParent, liveExists := yamlNodeAtPathSegments(liveRoot, path[:len(path)-1])
	originalParent, originalExists := yamlNodeAtPathSegments(originalRoot, path[:len(path)-1])
	if !liveExists || !originalExists || liveParent.Kind != yaml.MappingNode || originalParent.Kind != yaml.MappingNode {
		return
	}
	key := path[len(path)-1]
	findPair := func(mapping *yaml.Node) (*yaml.Node, *yaml.Node) {
		for index := len(mapping.Content) - 2; index >= 0; index -= 2 {
			if isStringMappingKey(mapping.Content[index], key) {
				return mapping.Content[index], mapping.Content[index+1]
			}
		}
		return nil, nil
	}
	liveKey, liveValue := findPair(liveParent)
	originalKey, originalValue := findPair(originalParent)
	copyComments := func(destination, source *yaml.Node) {
		if destination == nil || source == nil {
			return
		}
		if destination.HeadComment == "" {
			destination.HeadComment = source.HeadComment
		}
		if destination.LineComment == "" {
			destination.LineComment = source.LineComment
		}
		if destination.FootComment == "" {
			destination.FootComment = source.FootComment
		}
	}
	copyComments(liveKey, originalKey)
	if originalValue != nil && originalValue.Kind == yaml.ScalarNode && liveValue != nil &&
		(liveValue.Kind == yaml.MappingNode || liveValue.Kind == yaml.SequenceNode) && len(liveValue.Content) > 0 {
		lineComment := originalValue.LineComment
		originalWithoutLineComment := cloneYAMLNodeGraph(originalValue)
		originalWithoutLineComment.LineComment = ""
		copyComments(liveValue, originalWithoutLineComment)
		if liveKey != nil && liveKey.LineComment == "" {
			liveKey.LineComment = lineComment
		}
	} else {
		copyComments(liveValue, originalValue)
	}
}

// hasNodeRewriteIntentAtOrBelow reports whether an edit explicitly replaced the
// node at path or one of its descendants. It is used to distinguish an ordinary
// sequence index shift (which should rebase existing intents) from removal of a
// node that itself owns a replacement history (whose origin must remain at the
// now-vacant index for a possible re-add).
func hasNodeRewriteIntentAtOrBelow(st *docState, path []string) bool {
	if st == nil {
		return false
	}
	for encoded := range st.nodeRewriteIntents {
		segments, ok := splitJoinedPath(encoded)
		if ok && len(segments) >= len(path) && pathSegmentsEqual(segments[:len(path)], path) {
			return true
		}
	}
	return false
}

func (st *docState) root() *yaml.Node {
	if st == nil {
		return nil
	}
	return st.doc.Value()
}

// Information about a sequence under a mapping path in the original YAML.
type seqItemInfo struct {
	name  string // identity: value of "name" key if mapping, or scalar value itself (for fallback matching)
	start int    // byte offset at the beginning of the item's first line ("- " ...)
	end   int    // byte offset of the newline ending the last line of the item
}

// Boundaries of a "key: value" block for deletion.
type kvBounds struct {
	start         int // start offset of the line where the key begins (keyLineStart)
	end           int // exclusive end offset of the block (includes trailing newline if present)
	anchor        string
	collectionTag string // explicit/custom tag on a mapping or sequence value
	lineComment   string // parser-recognized inline comment on the original entry
}

type seqInfo struct {
	indent         int // spaces before '-' on the first line of an item
	itemKVIndent   int // spaces for subsequent key lines inside an item
	firstItemStart int // byte offset of the first item's line start
	lastItemEnd    int // byte offset of the newline ending the last item's last line
	hasAnyItem     bool
	originalPath   bool
	firstKeyInline bool          // whether first key (or scalar value) appears on the same line as "- "
	keyOrder       []string      // preferred key order for items (captured from an existing item)
	items          []seqItemInfo // per-item positions and names
	gaps           [][]byte      // raw bytes between items; len = len(items)-1
}

func cloneSeqIndex(in map[string]*seqInfo) map[string]*seqInfo {
	out := make(map[string]*seqInfo, len(in))
	for k, v := range in {
		cp := *v
		cp.keyOrder = append([]string(nil), v.keyOrder...)
		if v.items != nil {
			cp.items = make([]seqItemInfo, len(v.items))
			copy(cp.items, v.items)
		}
		if v.gaps != nil {
			cp.gaps = make([][]byte, len(v.gaps))
			for i := range v.gaps {
				if v.gaps[i] != nil {
					cp.gaps[i] = append([]byte(nil), v.gaps[i]...)
				}
			}
		}
		out[k] = &cp
	}
	return out
}

func cloneBoundsIndex(in map[string][]kvBounds) map[string][]kvBounds {
	out := make(map[string][]kvBounds, len(in))
	for k, v := range in {
		cp := make([]kvBounds, len(v))
		copy(cp, v)
		out[k] = cp
	}
	return out
}

// Information about a mapping block in the original YAML.
type mapInfo struct {
	indent       int // indent (in spaces) of keys inside this mapping
	lastLineEnd  int // byte offset of the newline that ends the last key/value line in this mapping
	hasAnyKey    bool
	originalPath bool // mapping existed in the original bytes
}

// One occurrence of "key: value" or "- value" in the original file.
type valueOcc struct {
	keyLineStart int // start offset of the line where the key/item begins
	valStart     int // start offset of the value token
	valEnd       int // end offset (exclusive) of the value token
	lineEnd      int // offset of '\n' ending this line (or len(original)-1 if final line has no \n)
	tag          string
	explicitTag  bool
	blockStyle   bool
	multiline    bool
}

// Global registry so we can look up state by *yaml.Node (doc).
var (
	regMu sync.Mutex
	reg   = map[weak.Pointer[yaml.Node]]*docState{}
)

// findOwnerByMapNode safely finds the docState that knows about mapNode,
// without holding regMu while touching per-state fields.
func findOwnerByMapNode(mapNode *yaml.Node) (*docState, *yaml.Node, []string, bool) {
	if mapNode == nil {
		return nil, nil, nil, false
	}

	// Snapshot states under regMu
	regMu.Lock()
	states := make([]*docState, 0, len(reg))
	for _, s := range reg {
		states = append(states, s)
	}
	regMu.Unlock()

	// First, try the fast path: lookup by handle → path mapping.
	for _, s := range states {
		s.mu.RLock()
		if p, ok := s.subPathByHN[weak.Make(mapNode)]; ok {
			doc := s.doc.Value()
			if doc != nil && len(doc.Content) > 0 {
				if exact, reachable := addressableTokenPathToNode(doc.Content[0], mapNode); reachable {
					if base, mappingOnly := mappingOnlyTokenPath(exact); mappingOnly && pathSegmentsEqual(base, p) {
						s.mu.RUnlock()
						return s, doc, base, true
					}
				}
			}
		}
		s.mu.RUnlock()
	}

	// Slow path: for mapping nodes that live inside sequences, we don't have
	// an entry in subPathByHN. In that case, scan the document AST for the
	// exact *yaml.Node pointer to discover which docState owns it.
	for _, s := range states {
		s.mu.RLock()
		doc := s.doc.Value()
		found := doc != nil && len(doc.Content) > 0 && contentNodeReachable(doc.Content[0], mapNode)
		s.mu.RUnlock()
		if found {
			return s, doc, nil, true
		}
	}
	return nil, nil, nil, false
}

// findOwnerByMapNodeTokens is the index-aware owner lookup used for mapping
// nodes nested inside sequences. subPathByHN intentionally stores only plain
// mapping paths, so callers that need an exact logical path must include array
// indices discovered from the AST.
func findOwnerByMapNodeTokens(mapNode *yaml.Node) (*docState, *yaml.Node, []ptrToken, bool) {
	if mapNode == nil {
		return nil, nil, nil, false
	}

	regMu.Lock()
	states := make([]*docState, 0, len(reg))
	for _, st := range reg {
		states = append(states, st)
	}
	regMu.Unlock()

	for _, st := range states {
		st.mu.RLock()
		doc := st.doc.Value()
		if doc != nil && len(doc.Content) > 0 {
			if path, ok := addressableTokenPathToNode(doc.Content[0], mapNode); ok {
				st.mu.RUnlock()
				return st, doc, path, true
			}
		}
		st.mu.RUnlock()
	}
	return nil, nil, nil, false
}

// findRegisteredNodeOwner identifies whether node belongs to a registered
// document without inspecting any fields on node. This matters for entry points
// that may receive a mapping handle while another goroutine changes that node's
// shape under the document lock: reading node.Kind before finding the owner
// would itself race with the mutation.
//
// The returned isDocument bit distinguishes the registered document handle
// from a node found in its AST. Callers must still acquire st.mu and revalidate
// the node before reading it or acting on the returned ownership information.
func findRegisteredNodeOwner(node *yaml.Node) (st *docState, doc *yaml.Node, isDocument bool, ok bool) {
	if node == nil {
		return nil, nil, false, false
	}
	if st, ok := lookup(node); ok {
		return st, node, true, true
	}
	if st, doc, _, ok = findOwnerByMapNodeTokens(node); ok {
		return st, doc, false, true
	}
	// A node can be reachable only through a non-string YAML key, which has no
	// JSON/object path representation. Still report its ownership so callers
	// acquire the document lock and then reject the unaddressable handle safely
	// instead of treating it as an unrelated standalone node.
	st, doc, _, ok = findOwnerByMapNode(node)
	return st, doc, false, ok
}

// contentNodeReachable scans only Content edges. Public yaml.Node trees are
// mutable, so ownership discovery must tolerate malformed cycles rather than
// recurse forever before the API can reject or ignore the caller's handle.
func contentNodeReachable(root, target *yaml.Node) bool {
	if root == nil || target == nil {
		return false
	}
	stack := []*yaml.Node{root}
	seen := make(map[*yaml.Node]struct{})
	for len(stack) > 0 {
		last := len(stack) - 1
		node := stack[last]
		stack = stack[:last]
		if node == nil {
			continue
		}
		if node == target {
			return true
		}
		if _, visited := seen[node]; visited {
			continue
		}
		seen[node] = struct{}{}
		stack = append(stack, node.Content...)
	}
	return false
}

type ownershipPathFrame struct {
	node   *yaml.Node
	parent *ownershipPathFrame
	token  ptrToken
	depth  int
}

func ownershipPath(frame *ownershipPathFrame) []ptrToken {
	path := make([]ptrToken, frame.depth)
	for frame.parent != nil {
		path[frame.depth-1] = frame.token
		frame = frame.parent
	}
	return path
}

func tokenPathToNode(root, target *yaml.Node, prefix []ptrToken) ([]ptrToken, bool) {
	if root == nil || target == nil {
		return nil, false
	}
	base := &ownershipPathFrame{node: root}
	stack := []*ownershipPathFrame{base}
	seen := make(map[*yaml.Node]struct{})
	for len(stack) > 0 {
		last := len(stack) - 1
		frame := stack[last]
		stack = stack[:last]
		node := frame.node
		if node == nil {
			continue
		}
		if node == target {
			path := append([]ptrToken(nil), prefix...)
			return append(path, ownershipPath(frame)...), true
		}
		if _, visited := seen[node]; visited {
			continue
		}
		seen[node] = struct{}{}

		switch node.Kind {
		case yaml.MappingNode:
			// Push children in reverse source order so the LIFO traversal retains
			// the recursive implementation's first-to-last search order.
			for i := (len(node.Content)/2 - 1) * 2; i >= 0; i -= 2 {
				key, value := node.Content[i], node.Content[i+1]
				if key == nil || value == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
					continue
				}
				stack = append(stack, &ownershipPathFrame{
					node: value, parent: frame, token: ptrToken{key: key.Value}, depth: frame.depth + 1,
				})
			}
		case yaml.SequenceNode:
			for index := len(node.Content) - 1; index >= 0; index-- {
				stack = append(stack, &ownershipPathFrame{
					node: node.Content[index], parent: frame,
					token: ptrToken{key: strconv.Itoa(index), isIdx: true, index: index}, depth: frame.depth + 1,
				})
			}
		}
	}
	return nil, false
}

func addressableTokenPathToNode(root, target *yaml.Node) ([]ptrToken, bool) {
	path, ok := tokenPathToNode(root, target, nil)
	if !ok {
		return nil, false
	}
	resolved, ok := nodeAtTokenPath(root, path)
	if !ok || resolved != target {
		return nil, false
	}
	return path, true
}

func nodeAtTokenPath(cur *yaml.Node, path []ptrToken) (*yaml.Node, bool) {
	for _, token := range path {
		if cur == nil {
			return nil, false
		}
		switch cur.Kind {
		case yaml.MappingNode:
			var child *yaml.Node
			for i := len(cur.Content) - 2; i >= 0; i -= 2 {
				if isStringMappingKey(cur.Content[i], token.key) {
					child = cur.Content[i+1]
					break
				}
			}
			if child == nil {
				return nil, false
			}
			cur = child
		case yaml.SequenceNode:
			if !token.isIdx || token.append || token.index < 0 || token.index >= len(cur.Content) {
				return nil, false
			}
			cur = cur.Content[token.index]
		default:
			return nil, false
		}
	}
	return cur, true
}

func tokenPathSegments(path []ptrToken) []string {
	out := make([]string, 0, len(path))
	for _, token := range path {
		if token.isIdx {
			out = append(out, indexSeg(token.index))
		} else {
			out = append(out, token.key)
		}
	}
	return out
}

func register(doc *yaml.Node, st *docState) {
	key := weak.Make(doc)
	regMu.Lock()
	reg[key] = st
	regMu.Unlock()

	runtime.AddCleanup(doc, func(key weak.Pointer[yaml.Node]) {
		regMu.Lock()
		delete(reg, key)
		regMu.Unlock()
	}, key)
	runtime.KeepAlive(doc)
}

func lookup(doc *yaml.Node) (*docState, bool) {
	regMu.Lock()
	st, ok := reg[weak.Make(doc)]
	regMu.Unlock()
	runtime.KeepAlive(doc)
	return st, ok
}
