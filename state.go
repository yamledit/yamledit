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
	mu          sync.RWMutex
	doc         weak.Pointer[yaml.Node]              // weak reference to the root document
	indent      int                                  // detected indent (2,3,4,...)
	indentSeq   bool                                 // whether sequences under a key are indented
	ordered     gyaml.MapSlice                       // current ordered mapping we edit (live view)
	comments    gyaml.CommentMap                     // captured comments (for fallback encode)
	subPathByHN map[weak.Pointer[yaml.Node]][]string // weak mapping-handle -> path segments

	// --- Byte-surgical indices ---
	original []byte // original file bytes (exact)
	// originalRootEmpty records a non-empty source document whose root was an
	// explicit empty mapping (for example "{}"). Such a document has no byte
	// insertion anchor, so the first real edit must use the standard encoder.
	originalRootEmpty bool
	originalTriviaOnly bool
	rootTokenStart    int
	rootTokenEnd      int
	lineOffsets       []int // starting offset of each line in original
	origOrdered       gyaml.MapSlice

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

	// explicit deletions requested (path\0key)
	toDelete        map[string]struct{}
	structuralDirty bool // when true, skip surgery and fall back to full encode
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
		found := false
		var walk func(*yaml.Node)
		walk = func(n *yaml.Node) {
			if n == nil || found {
				return
			}
			if n == mapNode {
				found = true
				return
			}
			for _, c := range n.Content {
				walk(c)
				if found {
					return
				}
			}
		}
		if doc != nil && len(doc.Content) > 0 {
			walk(doc.Content[0])
		}
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

func tokenPathToNode(cur, target *yaml.Node, path []ptrToken) ([]ptrToken, bool) {
	if cur == nil {
		return nil, false
	}
	if cur == target {
		return append([]ptrToken(nil), path...), true
	}
	switch cur.Kind {
	case yaml.MappingNode:
		for i := 0; i+1 < len(cur.Content); i += 2 {
			key, value := cur.Content[i], cur.Content[i+1]
			if key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
				continue
			}
			next := append(append([]ptrToken(nil), path...), ptrToken{key: key.Value})
			if found, ok := tokenPathToNode(value, target, next); ok {
				return found, true
			}
		}
	case yaml.SequenceNode:
		for i, value := range cur.Content {
			next := append(append([]ptrToken(nil), path...), ptrToken{key: strconv.Itoa(i), isIdx: true, index: i})
			if found, ok := tokenPathToNode(value, target, next); ok {
				return found, true
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
