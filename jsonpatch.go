package yamledit

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/big"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"unicode/utf8"

	jsonpatch "github.com/evanphx/json-patch/v5"
	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// JSON Patch (RFC-6902) public API
// --------------------------------------------------------------------------------------

// ApplyJSONPatchBytes applies a JSON Patch (as raw JSON) to a YAML node.
// Paths are resolved relative to 'node' (DocumentNode or MappingNode).
func ApplyJSONPatchBytes(node *yaml.Node, patchJSON []byte) error {
	return ApplyJSONPatchAtPathBytes(node, patchJSON, nil)
}

// ApplyJSONPatch applies a github.com/evanphx/json-patch/v5 Patch to a YAML node.
// Internally this marshals the patch back to JSON and delegates to ApplyJSONPatchBytes.
func ApplyJSONPatch(node *yaml.Node, patch jsonpatch.Patch) error {
	b, err := json.Marshal(patch)
	if err != nil {
		return fmt.Errorf("yamledit: cannot marshal jsonpatch.Patch; pass bytes instead: %w", err)
	}
	return ApplyJSONPatchBytes(node, b)
}

// ApplyJSONPatchAtPathBytes applies a JSON Patch, treating each op's path as relative
// to the given basePath (sequence of mapping keys).
func ApplyJSONPatchAtPathBytes(node *yaml.Node, patchJSON []byte, basePath []string) error {
	if !utf8.Valid(patchJSON) {
		return errors.New("yamledit: invalid JSON Patch: input is not valid UTF-8")
	}
	ops, err := decodePatchOps(patchJSON)
	if err != nil {
		return err
	}
	return applyDecodedPatch(node, ops, basePath)
}

// ApplyJSONPatchAtPath is a convenience wrapper for jsonpatch.Patch.
func ApplyJSONPatchAtPath(node *yaml.Node, patch jsonpatch.Patch, basePath []string) error {
	b, err := json.Marshal(patch)
	if err != nil {
		return fmt.Errorf("yamledit: cannot marshal jsonpatch.Patch; pass bytes instead: %w", err)
	}
	return ApplyJSONPatchAtPathBytes(node, b, basePath)
}

// --------------------------------------------------------------------------------------
// JSON Patch internals
// --------------------------------------------------------------------------------------

type patchOp struct {
	Op    string          `json:"op"`
	Path  string          `json:"path"`
	Value json.RawMessage `json:"value,omitempty"`
	From  string          `json:"from,omitempty"`

	hasValue bool
	hasFrom  bool
}

func (op *patchOp) UnmarshalJSON(data []byte) error {
	dec := json.NewDecoder(bytes.NewReader(data))
	first, err := dec.Token()
	if err != nil {
		return err
	}
	if delim, ok := first.(json.Delim); !ok || delim != '{' {
		return errors.New("operation must be an object")
	}

	// Do not decode through a map: JSON permits duplicate object member names,
	// while RFC 6902 requires exactly one occurrence of each member defined for
	// the selected operation. Keep every occurrence until op is known; members
	// irrelevant to that operation are ignored as RFC 6902 requires.
	members := make(map[string]json.RawMessage)
	memberCounts := make(map[string]int)
	for dec.More() {
		nameToken, err := dec.Token()
		if err != nil {
			return err
		}
		name, ok := nameToken.(string)
		if !ok {
			return errors.New("operation member name must be a string")
		}
		var raw json.RawMessage
		if err := dec.Decode(&raw); err != nil {
			return err
		}
		switch name {
		case "op", "path", "value", "from":
			memberCounts[name]++
			members[name] = append(json.RawMessage(nil), raw...)
		}
	}
	if _, err := dec.Token(); err != nil { // closing '}'
		return err
	}

	// A decoder may reuse a destination. Reset presence flags and raw fields so
	// an omitted member cannot inherit state from an earlier operation.
	*op = patchOp{}
	decodeRequiredString := func(name string) (string, error) {
		raw, ok := members[name]
		if !ok {
			return "", fmt.Errorf("missing required member %q", name)
		}
		if bytes.Equal(bytes.TrimSpace(raw), []byte("null")) {
			return "", fmt.Errorf("member %q must be a string", name)
		}
		var value string
		if err := json.Unmarshal(raw, &value); err != nil {
			return "", fmt.Errorf("member %q must be a string: %w", name, err)
		}
		return value, nil
	}

	if op.Op, err = decodeRequiredString("op"); err != nil {
		return err
	}
	if op.Path, err = decodeRequiredString("path"); err != nil {
		return err
	}
	if memberCounts["op"] != 1 {
		return errors.New("duplicate member \"op\"")
	}
	if memberCounts["path"] != 1 {
		return errors.New("duplicate member \"path\"")
	}
	if (op.Op == "add" || op.Op == "replace" || op.Op == "test") && memberCounts["value"] > 1 {
		return errors.New("duplicate member \"value\"")
	}
	if (op.Op == "move" || op.Op == "copy") && memberCounts["from"] > 1 {
		return errors.New("duplicate member \"from\"")
	}
	if raw, ok := members["value"]; ok {
		op.Value = append(op.Value[:0], raw...)
		op.hasValue = true
	}
	if raw, ok := members["from"]; ok && (op.Op == "move" || op.Op == "copy") {
		if bytes.Equal(bytes.TrimSpace(raw), []byte("null")) {
			return errors.New("member \"from\" must be a string")
		}
		if err := json.Unmarshal(raw, &op.From); err != nil {
			return fmt.Errorf("member \"from\" must be a string: %w", err)
		}
		op.hasFrom = true
	}
	return nil
}

func decodePatchOps(b []byte) ([]patchOp, error) {
	var ops []patchOp
	dec := json.NewDecoder(bytes.NewReader(b))
	if err := dec.Decode(&ops); err != nil {
		return nil, fmt.Errorf("yamledit: invalid JSON Patch: %w", err)
	}
	if ops == nil {
		return nil, errors.New("yamledit: JSON Patch must be an array")
	}
	for i, op := range ops {
		switch op.Op {
		case "add", "replace", "test":
			if !op.hasValue {
				return nil, fmt.Errorf("yamledit: JSON Patch operation %d (%s) is missing required member \"value\"", i, op.Op)
			}
		case "move", "copy":
			if !op.hasFrom {
				return nil, fmt.Errorf("yamledit: JSON Patch operation %d (%s) is missing required member \"from\"", i, op.Op)
			}
		}
	}
	var trailing interface{}
	if err := dec.Decode(&trailing); err != io.EOF {
		if err == nil {
			err = errors.New("unexpected trailing JSON value")
		}
		return nil, fmt.Errorf("yamledit: invalid JSON Patch: %w", err)
	}
	return ops, nil
}

// ptrToken models one JSON Pointer segment: either a mapping key or an array index/append.
type ptrToken struct {
	key    string
	index  int
	isIdx  bool
	append bool // only valid for add into arrays
}

func parseJSONPointer(p string) ([]ptrToken, error) {
	if p == "" {
		// The empty string is the root pointer. "/" instead addresses an
		// object member whose key is the empty string.
		return []ptrToken{}, nil
	}
	if !strings.HasPrefix(p, "/") {
		return nil, fmt.Errorf("yamledit: JSON Pointer must start with '/': %q", p)
	}
	parts := strings.Split(p, "/")[1:]
	toks := make([]ptrToken, 0, len(parts))
	for _, s := range parts {
		seg, err := unescapeJSONPointerToken(s)
		if err != nil {
			return nil, err
		}
		if seg == "-" {
			toks = append(toks, ptrToken{key: seg, isIdx: true, append: true})
			continue
		}
		// Classify a syntactically valid RFC 6902 array index, while retaining
		// the raw key. Container type decides whether "0" is an index or an
		// object member name.
		if isJSONArrayIndex(seg) {
			if i, err := strconv.Atoi(seg); err == nil {
				toks = append(toks, ptrToken{key: seg, isIdx: true, index: i})
				continue
			}
		}
		toks = append(toks, ptrToken{key: seg})
	}
	return toks, nil
}

func unescapeJSONPointerToken(s string) (string, error) {
	var out strings.Builder
	for i := 0; i < len(s); i++ {
		if s[i] != '~' {
			out.WriteByte(s[i])
			continue
		}
		if i+1 >= len(s) || (s[i+1] != '0' && s[i+1] != '1') {
			return "", fmt.Errorf("yamledit: invalid JSON Pointer escape in %q", s)
		}
		i++
		if s[i] == '0' {
			out.WriteByte('~')
		} else {
			out.WriteByte('/')
		}
	}
	return out.String(), nil
}

func isJSONArrayIndex(s string) bool {
	if s == "0" {
		return true
	}
	if len(s) == 0 || s[0] < '1' || s[0] > '9' {
		return false
	}
	for i := 1; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return false
		}
	}
	return true
}

// applyDecodedPatch executes ops in-order, relative to basePath.
func applyDecodedPatch(node *yaml.Node, ops []patchOp, basePath []string) error {
	if node == nil {
		return errors.New("yamledit: nil node")
	}

	// Discover registered ownership without reading fields on node. A mapping
	// handle can be converted to another YAML kind by a concurrent state-aware
	// edit, so even reading node.Kind must happen under the owning document lock.
	st, docHN, isDocument, registered := findRegisteredNodeOwner(node)
	var startMap *yaml.Node
	var baseFromRoot []ptrToken
	var err error
	if registered {
		// Protect both the yaml.Node tree and its ordered shadow for the entire
		// patch, including classification and validation of the starting node.
		st.mu.Lock()
		defer st.mu.Unlock()
		startMap, baseFromRoot, err = resolveRegisteredStartLocked(node, st, docHN, isDocument)
		if err == nil {
			// Resolve the handle first so a concurrently converted MappingNode can
			// report its ordinary wrong-kind error. Once the target is confirmed as
			// a mapping, validate the complete owning document: an alias elsewhere
			// can target this subtree, and malformed Content must be rejected before
			// graph cloning or mutation.
			if validateErr := validateYAMLMarshalDocument(docHN); validateErr != nil {
				err = fmt.Errorf("yamledit: cannot apply JSON Patch to malformed YAML: %w", validateErr)
			} else {
				noteDirectASTMutationLocked(st)
			}
		}
	} else {
		// Nodes that were not returned by Parse have no shared docState contract,
		// so validate their shape explicitly before cloning or mutation.
		startMap, err = resolveUnregisteredStart(node)
		if err == nil {
			if node.Kind == yaml.DocumentNode {
				err = validateYAMLMarshalDocument(node)
			} else {
				err = validateYAMLContentTree(node)
			}
			if err != nil {
				err = fmt.Errorf("yamledit: cannot apply JSON Patch to malformed YAML: %w", err)
			}
		}
	}
	if err != nil {
		return err
	}
	if startMap == nil {
		return errors.New("yamledit: could not resolve starting mapping")
	}
	if !registered {
		// Operations on an unregistered node should not accidentally receive a
		// stale registry state from the declarations above.
		st = nil
		docHN = nil
		baseFromRoot = nil
	}
	baseTokens := make([]ptrToken, 0, len(basePath))
	for _, k := range basePath {
		baseTokens = append(baseTokens, ptrToken{key: k})
	}

	// JSON Patch is atomic: validate the full, sequential operation list on a
	// graph-preserving clone before touching the live AST. This also catches
	// ordered-shadow update failures for registered documents. Without this
	// pass, an early successful operation remained visible when a later test or
	// path lookup failed.
	preflightStart := cloneYAMLNodeGraph(startMap)
	var preflightDoc *yaml.Node
	var preflightState *docState
	if st != nil {
		// Clone the complete document, not just the selected mapping. Alias nodes
		// outside a mapping handle can still point at anchors inside it, and those
		// references must participate in the atomic preflight.
		var cloned map[*yaml.Node]*yaml.Node
		preflightDoc, cloned = cloneYAMLNodeGraphWithMap(docHN)
		preflightStart = cloned[startMap]
		if preflightDoc == nil || preflightStart == nil {
			return errors.New("yamledit: could not clone document for JSON Patch preflight")
		}
		preflightState = &docState{ordered: cloneMapSlice(st.ordered)}
	}
	if err := executeDecodedPatch(preflightStart, preflightState, preflightDoc, baseFromRoot, ops, baseTokens); err != nil {
		return err
	}
	// Replacing an ancestor can remove an anchored descendant while leaving an
	// alias elsewhere in the document pointing at the now-detached node. The
	// individual operation cannot reliably see every external alias when the
	// patch starts at a nested mapping, so validate the complete cloned graph at
	// the atomic preflight boundary before making the same edits to the live AST.
	preflightRoot := preflightStart
	if preflightDoc != nil {
		preflightRoot = preflightDoc
	}
	if err := validateYAMLAliasGraph(preflightRoot); err != nil {
		return fmt.Errorf("yamledit: JSON Patch would produce an invalid YAML alias graph: %w", err)
	}
	if err := executeDecodedPatch(startMap, st, docHN, baseFromRoot, ops, baseTokens); err != nil {
		return err
	}
	if st != nil {
		st.expectedAST = cloneYAMLNodeGraph(docHN)
	}
	return nil
}

func executeDecodedPatch(startMap *yaml.Node, st *docState, docHN *yaml.Node, baseFromRoot []ptrToken, ops []patchOp, baseTokens []ptrToken) error {
	for _, op := range ops {
		segPath, err := parseJSONPointer(op.Path)
		if err != nil {
			return err
		}
		// Prepend basePath (mapping segments only).
		combined := make([]ptrToken, 0, len(baseTokens)+len(segPath))
		combined = append(combined, baseTokens...)
		combined = append(combined, segPath...)

		switch op.Op {
		case "test":
			if err := opTest(startMap, combined, op.Value); err != nil {
				return err
			}
		case "add":
			if err := opAdd(startMap, st, docHN, baseFromRoot, combined, op.Value); err != nil {
				return err
			}
		case "remove":
			if err := opRemove(startMap, st, docHN, baseFromRoot, combined); err != nil {
				return err
			}
		case "replace":
			if err := opReplace(startMap, st, docHN, baseFromRoot, combined, op.Value); err != nil {
				return err
			}
		case "move":
			from, err := parseJSONPointer(op.From)
			if err != nil {
				return err
			}
			from = append(append([]ptrToken(nil), baseTokens...), from...)
			if err := opMove(startMap, st, docHN, baseFromRoot, from, combined); err != nil {
				return err
			}
		case "copy":
			from, err := parseJSONPointer(op.From)
			if err != nil {
				return err
			}
			from = append(append([]ptrToken(nil), baseTokens...), from...)
			if err := opCopy(startMap, st, docHN, baseFromRoot, from, combined); err != nil {
				return err
			}
		default:
			return fmt.Errorf("yamledit: unsupported op %q", op.Op)
		}
	}
	return nil
}

func cloneYAMLNodeGraph(root *yaml.Node) *yaml.Node {
	cloned, _ := cloneYAMLNodeGraphWithMap(root)
	return cloned
}

func cloneYAMLNodeGraphWithMap(root *yaml.Node) (*yaml.Node, map[*yaml.Node]*yaml.Node) {
	seen := make(map[*yaml.Node]*yaml.Node)
	var clone func(*yaml.Node) *yaml.Node
	clone = func(node *yaml.Node) *yaml.Node {
		if node == nil {
			return nil
		}
		if existing := seen[node]; existing != nil {
			return existing
		}
		copyNode := *node
		copyNode.Content = nil
		copyNode.Alias = nil
		seen[node] = &copyNode
		if len(node.Content) > 0 {
			copyNode.Content = make([]*yaml.Node, len(node.Content))
			for i, child := range node.Content {
				copyNode.Content[i] = clone(child)
			}
		}
		copyNode.Alias = clone(node.Alias)
		return &copyNode
	}
	return clone(root), seen
}

// resolveUnregisteredStart preserves JSON Patch support for standalone yaml.Node
// values. Registered nodes must instead be classified by
// resolveRegisteredStartLocked so their fields are never read outside st.mu.
func resolveUnregisteredStart(node *yaml.Node) (*yaml.Node, error) {
	switch node.Kind {
	case yaml.DocumentNode:
		if len(node.Content) != 1 || node.Content[0] == nil || node.Content[0].Kind != yaml.MappingNode {
			return nil, errors.New("yamledit: document root is not a mapping")
		}
		return node.Content[0], nil
	case yaml.MappingNode:
		return node, nil
	default:
		return nil, errors.New("yamledit: ApplyJSONPatch requires a DocumentNode or MappingNode")
	}
}

// resolveRegisteredStartLocked classifies and revalidates a registered patch
// target. The caller must hold st.mu for writing.
func resolveRegisteredStartLocked(node *yaml.Node, st *docState, docHN *yaml.Node, isDocument bool) (*yaml.Node, []ptrToken, error) {
	rootDoc := st.root()
	if rootDoc == nil || rootDoc != docHN {
		return nil, nil, errors.New("yamledit: document is no longer available")
	}
	if rootDoc.Kind != yaml.DocumentNode || len(rootDoc.Content) != 1 || rootDoc.Content[0] == nil || rootDoc.Content[0].Kind != yaml.MappingNode {
		return nil, nil, errors.New("yamledit: document root is not a mapping")
	}
	if isDocument {
		if node != rootDoc || node.Kind != yaml.DocumentNode {
			return nil, nil, errors.New("yamledit: document root is not a mapping")
		}
		return node.Content[0], nil, nil
	}
	if node.Kind != yaml.MappingNode {
		return nil, nil, errors.New("yamledit: ApplyJSONPatch requires a DocumentNode or MappingNode")
	}
	if exact, ok := addressableTokenPathToNode(rootDoc.Content[0], node); ok {
		return node, exact, nil
	}
	return nil, nil, errors.New("yamledit: starting mapping is no longer attached to the document")
}

// --- JSON → (ordered value, yaml.Node) helpers ---

func decodeJSONValue(raw json.RawMessage) (interface{}, error) {
	if raw == nil {
		return nil, errors.New("yamledit: missing 'value' for operation")
	}
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.UseNumber()
	var v interface{}
	if err := dec.Decode(&v); err != nil {
		return nil, fmt.Errorf("yamledit: invalid JSON value: %w", err)
	}
	return v, nil
}

func jsonValueToOrdered(v interface{}) interface{} {
	switch t := v.(type) {
	case json.Number:
		// Keep the lexical JSON number. Converting through float64 silently
		// rounds large decimals and can turn a finite exponent into infinity.
		return t
	case float64, bool, string, nil:
		return t
	case []interface{}:
		out := make([]interface{}, 0, len(t))
		for _, e := range t {
			out = append(out, jsonValueToOrdered(e))
		}
		return out
	case map[string]interface{}:
		// order is not guaranteed in JSON; create a stable MapSlice (sorted keys)
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)

		ms := gyaml.MapSlice{}
		for _, k := range keys {
			ms = append(ms, gyaml.MapItem{Key: k, Value: jsonValueToOrdered(t[k])})
		}
		return ms
	default:
		return t
	}
}

func jsonValueToYAMLNode(v interface{}) *yaml.Node {
	switch t := v.(type) {
	case nil:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!null", Value: "null"}
	case bool:
		if t {
			return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!bool", Value: "true"}
		}
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!bool", Value: "false"}
	case json.Number:
		tag := "!!int"
		if strings.ContainsAny(string(t), ".eE") {
			tag = "!!float"
		}
		node := &yaml.Node{Kind: yaml.ScalarNode, Tag: tag, Value: string(t)}
		if !yamlLexemeResolvesAsTag(string(t), tag) {
			node.Style |= yaml.TaggedStyle
		}
		return node
	case float64:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!float", Value: formatYAMLFloat(t)}
	case int:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.Itoa(t)}
	case int64:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatInt(t, 10)}
	case string:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: t}
	case []interface{}:
		seq := &yaml.Node{Kind: yaml.SequenceNode, Tag: "!!seq"}
		for _, e := range t {
			seq.Content = append(seq.Content, jsonValueToYAMLNode(e))
		}
		return seq
	case map[string]interface{}:
		mp := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
		for k, vv := range t {
			mp.Content = append(mp.Content, &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: k}, jsonValueToYAMLNode(vv))
		}
		return mp
	case gyaml.MapSlice:
		mp := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
		for _, it := range t {
			ks, _ := it.Key.(string)
			mp.Content = append(mp.Content, &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: ks}, jsonValueToYAMLNode(it.Value))
		}
		return mp
	default:
		// best-effort string
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: fmt.Sprint(t)}
	}
}

// yamlNodeToInterface converts a YAML node to canonical Go types for comparison.
func yamlNodeToInterface(n *yaml.Node) interface{} {
	budget := orderedShadowNodeBudget
	return yamlNodeToInterfaceSeen(n, make(map[*yaml.Node]bool), &budget)
}

func yamlNodeToInterfaceSeen(n *yaml.Node, visiting map[*yaml.Node]bool, budget *int) interface{} {
	if n == nil {
		return nil
	}
	if budget == nil || *budget <= 0 {
		return unsupportedJSONValue{"YAML graph exceeds JSON conversion limit"}
	}
	*budget = *budget - 1
	if visiting[n] {
		return unsupportedJSONValue{"recursive YAML alias"}
	}
	visiting[n] = true
	defer delete(visiting, n)
	switch n.Kind {
	case yaml.ScalarNode:
		switch n.Tag {
		case "!!null":
			return nil
		case "!!bool":
			var value bool
			if err := n.Decode(&value); err == nil {
				return value
			}
			switch strings.ToLower(strings.TrimSpace(n.Value)) {
			case "true", "y", "yes", "on":
				return true
			case "false", "n", "no", "off":
				return false
			default:
				return unsupportedJSONValue{"YAML boolean has an invalid spelling"}
			}
		case "!!int":
			// Preserve exact decimal integers where possible, while also honoring
			// YAML base prefixes and digit separators (0x10, 0o20, 1_000).
			decimal := strings.ReplaceAll(n.Value, "_", "")
			if i, err := strconv.ParseInt(decimal, 0, 64); err == nil {
				return int(i)
			}
			if u, err := strconv.ParseUint(decimal, 0, 64); err == nil {
				return u
			}
			return json.Number(decimal)
		case "!!float":
			decimal := strings.ReplaceAll(n.Value, "_", "")
			if _, ok := normalizeDecimalNumber(decimal); ok {
				return json.Number(decimal)
			}
			var decoded interface{}
			if err := n.Decode(&decoded); err == nil {
				if value, ok := decoded.(float64); ok {
					return value
				}
			}
			return n.Value
		default:
			return n.Value
		}
	case yaml.MappingNode:
		m := map[string]interface{}{}
		for i := 0; i+1 < len(n.Content); i += 2 {
			key := n.Content[i]
			if key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
				return unsupportedJSONValue{"YAML mapping has a non-string key"}
			}
			m[key.Value] = yamlNodeToInterfaceSeen(n.Content[i+1], visiting, budget)
		}
		return m
	case yaml.SequenceNode:
		arr := make([]interface{}, 0, len(n.Content))
		for _, c := range n.Content {
			arr = append(arr, yamlNodeToInterfaceSeen(c, visiting, budget))
		}
		return arr
	case yaml.AliasNode:
		return yamlNodeToInterfaceSeen(n.Alias, visiting, budget)
	default:
		return nil
	}
}

func lastStringMappingEntryIndexes(node *yaml.Node) map[string]int {
	if node == nil {
		return nil
	}
	indexes := make(map[string]int, len(node.Content)/2)

	// Walk paired mapping entries in reverse so the first index recorded for a
	// key is its semantically winning last occurrence. Derive an even starting
	// index so a malformed trailing key without a value is ignored just as it is
	// by the forward mapping walks in this file.
	start := len(node.Content) - 2
	if start >= 0 && start%2 != 0 {
		start--
	}
	for index := start; index >= 0; index -= 2 {
		key := node.Content[index]
		if key == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
			continue
		}
		if _, exists := indexes[key.Value]; !exists {
			indexes[key.Value] = index
		}
	}
	return indexes
}

type sequencePresentationCandidate struct {
	index int
	value interface{}
}

// replacementPresentationFingerprint groups values that can be equal under
// deepEqual. It is only an index key: callers must still compare candidates to
// make hash collisions harmless. The encoding mirrors deepEqual's numeric
// normalization and order-independent string-keyed mapping comparison.
func replacementPresentationFingerprint(value interface{}) uint64 {
	const (
		fnvOffset64 = uint64(14695981039346656037)
		fnvPrime64  = uint64(1099511628211)
	)

	hash := fnvOffset64
	writeByte := func(value byte) {
		hash ^= uint64(value)
		hash *= fnvPrime64
	}
	writeUint64 := func(value uint64) {
		for shift := uint(0); shift < 64; shift += 8 {
			writeByte(byte(value >> shift))
		}
	}
	writeString := func(value string) {
		writeUint64(uint64(len(value)))
		for index := 0; index < len(value); index++ {
			writeByte(value[index])
		}
	}

	// Sequence reconciliation passes yamlNodeToInterface results, whose nested
	// maps and slices are already plain. Retain one top-level normalization for
	// consistency with deepEqual without repeatedly walking every subtree.
	value = toPlain(value)
	var visit func(interface{})
	visit = func(value interface{}) {
		if decimal, ok := canonicalDecimal(value); ok {
			writeByte('n')
			if decimal.negative {
				writeByte(1)
			} else {
				writeByte(0)
			}
			writeString(decimal.digits)
			writeString(decimal.scale)
			return
		}

		switch typed := value.(type) {
		case nil:
			writeByte('0')
		case bool:
			writeByte('b')
			if typed {
				writeByte(1)
			} else {
				writeByte(0)
			}
		case string:
			writeByte('s')
			writeString(typed)
		case map[string]interface{}:
			writeByte('m')
			writeUint64(uint64(len(typed)))
			keys := make([]string, 0, len(typed))
			for key := range typed {
				keys = append(keys, key)
			}
			sort.Strings(keys)
			for _, key := range keys {
				writeString(key)
				visit(typed[key])
			}
		case []interface{}:
			writeByte('a')
			writeUint64(uint64(len(typed)))
			for _, item := range typed {
				visit(item)
			}
		case unsupportedJSONValue:
			writeByte('x')
			writeString(typed.reason)
		default:
			// yamlNodeToInterface currently emits only the cases above. Keep an
			// equality-safe fallback for future types: values of the same type share
			// a bucket and deepEqual performs the authoritative comparison.
			writeByte('u')
			writeString(fmt.Sprintf("%T", typed))
		}
	}

	visit(value)
	return hash
}

// reconcileReplacementPresentation applies the package's key-order and comment
// policy to a JSON Patch replacement. JSON object order is not semantic, so
// members retained from the source keep their order and presentation while new
// members are appended in the deterministic order of the decoded JSON value.
// Tags and anchors are deliberately not copied here: replacement tag intent and
// alias validation remain authoritative.
func reconcileReplacementPresentation(oldNode, newNode *yaml.Node) {
	if oldNode == nil || newNode == nil {
		return
	}
	if newNode.HeadComment == "" {
		newNode.HeadComment = oldNode.HeadComment
	}
	if newNode.LineComment == "" {
		newNode.LineComment = oldNode.LineComment
	}
	if newNode.FootComment == "" {
		newNode.FootComment = oldNode.FootComment
	}
	if oldNode.Kind != newNode.Kind || oldNode.Tag != newNode.Tag {
		return
	}
	if deepEqual(yamlNodeToInterface(oldNode), yamlNodeToInterface(newNode)) {
		newNode.Style = oldNode.Style
	}

	switch newNode.Kind {
	case yaml.MappingNode:
		newByKey := lastStringMappingEntryIndexes(newNode)
		oldByKey := lastStringMappingEntryIndexes(oldNode)
		used := make(map[string]struct{}, len(newByKey))
		reordered := make([]*yaml.Node, 0, len(newNode.Content))
		for index := 0; index+1 < len(oldNode.Content); index += 2 {
			oldKey := oldNode.Content[index]
			if oldKey == nil || oldKey.Kind != yaml.ScalarNode || oldKey.Tag != "!!str" {
				continue
			}
			newIndex, exists := newByKey[oldKey.Value]
			if !exists {
				continue
			}
			// Earlier source duplicates are not retained by JSON object semantics;
			// the reverse index identifies the winning occurrence in constant time.
			if oldByKey[oldKey.Value] != index {
				continue
			}
			newKey, newValue := newNode.Content[newIndex], newNode.Content[newIndex+1]
			reconcileReplacementPresentation(oldKey, newKey)
			reconcileReplacementPresentation(oldNode.Content[index+1], newValue)
			reordered = append(reordered, newKey, newValue)
			used[oldKey.Value] = struct{}{}
		}
		for index := 0; index+1 < len(newNode.Content); index += 2 {
			key := newNode.Content[index]
			if key != nil && key.Kind == yaml.ScalarNode && key.Tag == "!!str" {
				if _, exists := used[key.Value]; exists {
					continue
				}
			}
			reordered = append(reordered, key, newNode.Content[index+1])
		}
		newNode.Content = reordered
	case yaml.SequenceNode:
		// Mapping records with a unique scalar "name" field retain presentation
		// independently of their index; other values are matched uniquely by their
		// logical JSON value.
		identity := func(node *yaml.Node) (string, bool) {
			if node == nil || node.Kind != yaml.MappingNode {
				return "", false
			}
			for index := len(node.Content) - 2; index >= 0; index -= 2 {
				if isStringMappingKey(node.Content[index], "name") {
					value := node.Content[index+1]
					if value != nil && value.Kind == yaml.ScalarNode {
						return value.Value, true
					}
				}
			}
			return "", false
		}
		oldByIdentity := make(map[string][]int, len(oldNode.Content))
		oldByLogicalValue := make(map[uint64][]sequencePresentationCandidate, len(oldNode.Content))
		usedOld := make(map[int]struct{}, len(newNode.Content))
		var mappingTemplate *yaml.Node
		for index, original := range oldNode.Content {
			if original != nil && original.Kind == yaml.MappingNode {
				if mappingTemplate == nil {
					mappingTemplate = original
				}
			}
			if name, ok := identity(original); ok {
				oldByIdentity[name] = append(oldByIdentity[name], index)
			}
			value := yamlNodeToInterface(original)
			fingerprint := replacementPresentationFingerprint(value)
			oldByLogicalValue[fingerprint] = append(oldByLogicalValue[fingerprint], sequencePresentationCandidate{
				index: index,
				value: value,
			})
		}
		reorderFromTemplate := func(template, current *yaml.Node) {
			if template == nil || current == nil || template.Kind != yaml.MappingNode || current.Kind != yaml.MappingNode {
				return
			}
			byKey := lastStringMappingEntryIndexes(current)
			used := make(map[string]struct{}, len(byKey))
			reordered := make([]*yaml.Node, 0, len(current.Content))
			for index := 0; index+1 < len(template.Content); index += 2 {
				key := template.Content[index]
				if key == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
					continue
				}
				currentIndex, exists := byKey[key.Value]
				if !exists {
					continue
				}
				reordered = append(reordered, current.Content[currentIndex], current.Content[currentIndex+1])
				used[key.Value] = struct{}{}
			}
			for index := 0; index+1 < len(current.Content); index += 2 {
				key := current.Content[index]
				if key != nil && key.Kind == yaml.ScalarNode && key.Tag == "!!str" {
					if _, exists := used[key.Value]; exists {
						continue
					}
				}
				reordered = append(reordered, key, current.Content[index+1])
			}
			current.Content = reordered
		}
		for _, current := range newNode.Content {
			match, matchCount := -1, 0
			if name, ok := identity(current); ok {
				matches := oldByIdentity[name]
				matchCount = len(matches)
				if matchCount == 1 {
					match = matches[0]
				}
			} else {
				currentValue := yamlNodeToInterface(current)
				fingerprint := replacementPresentationFingerprint(currentValue)
				for _, candidate := range oldByLogicalValue[fingerprint] {
					if deepEqual(candidate.value, currentValue) {
						match = candidate.index
						matchCount++
						if matchCount > 1 {
							break
						}
					}
				}
			}
			if matchCount != 1 {
				reorderFromTemplate(mappingTemplate, current)
				continue
			}
			if _, duplicate := usedOld[match]; duplicate {
				continue
			}
			usedOld[match] = struct{}{}
			reconcileReplacementPresentation(oldNode.Content[match], current)
		}
	}
}

type unsupportedJSONValue struct {
	reason string
}

func (v unsupportedJSONValue) MarshalJSON() ([]byte, error) {
	return nil, fmt.Errorf("yamledit: %s is not JSON-compatible", v.reason)
}

// --- Path resolution on YAML AST ---

// resolveParent locates the parent node for the final token.
// If createForAdd is true, it will EnsurePath for missing mapping segments (not arrays).
func resolveParent(start *yaml.Node, tokens []ptrToken, createForAdd bool) (parent *yaml.Node, last ptrToken, err error) {
	if start == nil {
		return nil, ptrToken{}, errors.New("yamledit: nil start node")
	}
	// normalize to mapping start
	var cur *yaml.Node
	switch start.Kind {
	case yaml.DocumentNode:
		if len(start.Content) == 0 || start.Content[0].Kind != yaml.MappingNode {
			return nil, ptrToken{}, errors.New("yamledit: document has no mapping root")
		}
		cur = start.Content[0]
	case yaml.MappingNode:
		cur = start
	default:
		return nil, ptrToken{}, errors.New("yamledit: start node must be DocumentNode or MappingNode")
	}
	if len(tokens) == 0 {
		return cur, ptrToken{}, nil
	}

	// walk up to parent
	for i := 0; i < len(tokens)-1; i++ {
		t := tokens[i]
		if cur.Kind == yaml.MappingNode {
			if hasNonStringMappingKeyNamed(cur, t.key) {
				return nil, ptrToken{}, fmt.Errorf("yamledit: path %q collides with a non-string YAML key", t.key)
			}
			// find mapping key
			var child *yaml.Node
			for j := len(cur.Content) - 2; j >= 0; j -= 2 {
				if isStringMappingKey(cur.Content[j], t.key) {
					child = cur.Content[j+1]
					break
				}
			}
			if child == nil {
				if !createForAdd {
					return nil, ptrToken{}, fmt.Errorf("yamledit: path not found at %q", t.key)
				}
				// create mapping
				key := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: t.key}
				val := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
				cur.Content = append(cur.Content, key, val)
				child = val
			}
			cur = child
		} else if cur.Kind == yaml.SequenceNode {
			if !t.isIdx || t.append {
				return nil, ptrToken{}, fmt.Errorf("yamledit: expected array index at segment %d", i)
			}
			if t.index < 0 || t.index >= len(cur.Content) {
				return nil, ptrToken{}, fmt.Errorf("yamledit: array index out of bounds at segment %d", i)
			}
			cur = cur.Content[t.index]
		} else {
			return nil, ptrToken{}, fmt.Errorf("yamledit: cannot traverse into node kind %v at segment %d", cur.Kind, i)
		}
	}
	last = tokens[len(tokens)-1]
	if cur.Kind == yaml.MappingNode && hasNonStringMappingKeyNamed(cur, last.key) {
		return nil, ptrToken{}, fmt.Errorf("yamledit: path %q collides with a non-string YAML key", last.key)
	}
	return cur, last, nil
}

func logicalPatchPathSegments(start *yaml.Node, baseFromRoot, tokens []ptrToken) ([]string, bool) {
	cur := start
	if cur != nil && cur.Kind == yaml.DocumentNode {
		if len(cur.Content) == 0 {
			return nil, false
		}
		cur = cur.Content[0]
	}
	out := append([]string(nil), tokenPathSegments(baseFromRoot)...)
	for index, token := range tokens {
		last := index == len(tokens)-1
		if cur == nil {
			return nil, false
		}
		switch cur.Kind {
		case yaml.MappingNode:
			out = append(out, token.key)
			if last {
				continue
			}
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
			if !token.isIdx || token.append && !last || token.index < 0 {
				return nil, false
			}
			itemIndex := token.index
			if token.append {
				itemIndex = len(cur.Content)
			}
			out = append(out, indexSeg(itemIndex))
			if last {
				continue
			}
			if itemIndex >= len(cur.Content) {
				return nil, false
			}
			cur = cur.Content[itemIndex]
		default:
			return nil, false
		}
	}
	return out, true
}

func scalarTagForOrderedValue(value interface{}) (string, bool) {
	return scalarYAMLTag(value)
}

func markPatchScalarTagChange(st *docState, destinationPath []string, old *yaml.Node, value interface{}) {
	if st == nil || len(destinationPath) == 0 || old == nil || old.Kind != yaml.ScalarNode {
		return
	}
	newTag, ok := scalarTagForOrderedValue(value)
	if ok && old.Tag != newTag {
		setForcedScalarIntentLocked(st, destinationPath, newTag)
	}
}

func markPatchSequenceScalarInsertion(st *docState, destinationPath []string, value interface{}) {
	if st == nil || len(destinationPath) == 0 {
		return
	}
	newTag, ok := scalarTagForOrderedValue(value)
	if !ok {
		return
	}
	// Consult the immutable source AST rather than the scalar byte index. The
	// latter deliberately omits scalar items in mixed sequences, but an inserted
	// scalar can still temporarily occupy an original custom-tagged index and
	// later become its net replacement after another item is removed.
	originalRoot := st.originalAST
	if originalRoot != nil && originalRoot.Kind == yaml.DocumentNode && len(originalRoot.Content) == 1 {
		originalRoot = originalRoot.Content[0]
	}
	original, exists := yamlNodeAtPathSegments(originalRoot, destinationPath)
	if exists && original.Kind == yaml.ScalarNode && original.Tag != newTag {
		setForcedScalarIntentLocked(st, destinationPath, newTag)
	}
}

func clearForcedScalarIntentAtOrBelow(st *docState, path []string) {
	if st == nil || len(path) == 0 {
		return
	}
	for encoded := range st.forceScalarRewrite {
		segments, ok := splitJoinedPath(encoded)
		if ok && len(segments) >= len(path) && pathSegmentsEqual(segments[:len(path)], path) {
			delete(st.forceScalarRewrite, encoded)
			delete(st.forceScalarTags, encoded)
		}
	}
}

func rebaseForcedScalarIntentsForSequence(st *docState, sequencePath []string, index, delta int, removeIndex bool) {
	if st == nil || len(st.forceScalarRewrite) == 0 {
		return
	}
	rebased := make(map[string]struct{}, len(st.forceScalarRewrite))
	tags := make(map[string]string, len(st.forceScalarTags))
	for encoded := range st.forceScalarRewrite {
		segments, ok := splitJoinedPath(encoded)
		if !ok || len(segments) <= len(sequencePath) || !pathSegmentsEqual(segments[:len(sequencePath)], sequencePath) ||
			!isIndexPathSegment(segments[len(sequencePath)]) {
			rebased[encoded] = struct{}{}
			tags[encoded] = st.forceScalarTags[encoded]
			continue
		}
		itemIndex, err := strconv.Atoi(segments[len(sequencePath)][1 : len(segments[len(sequencePath)])-1])
		if err != nil || removeIndex && itemIndex == index {
			if err != nil {
				rebased[encoded] = struct{}{}
				tags[encoded] = st.forceScalarTags[encoded]
			}
			continue
		}
		if itemIndex > index || (!removeIndex && itemIndex >= index) {
			segments[len(sequencePath)] = indexSeg(itemIndex + delta)
			newEncoded := joinPath(segments)
			rebased[newEncoded] = struct{}{}
			tags[newEncoded] = st.forceScalarTags[encoded]
			continue
		}
		rebased[encoded] = struct{}{}
		tags[encoded] = st.forceScalarTags[encoded]
	}
	st.forceScalarRewrite = rebased
	st.forceScalarTags = tags
}

func rebaseNodeRewriteIntentsForSequence(st *docState, sequencePath []string, index, delta int, removeIndex, removalLeavesVacancy bool) {
	if st == nil || len(st.nodeRewriteIntents) == 0 {
		return
	}
	rebased := make(map[string]nodeRewriteIntent, len(st.nodeRewriteIntents))
	for encoded, intent := range st.nodeRewriteIntents {
		segments, ok := splitJoinedPath(encoded)
		if !ok || len(segments) <= len(sequencePath) || !pathSegmentsEqual(segments[:len(sequencePath)], sequencePath) ||
			!isIndexPathSegment(segments[len(sequencePath)]) {
			rebased[encoded] = intent
			continue
		}
		itemIndex, err := strconv.Atoi(segments[len(sequencePath)][1 : len(segments[len(sequencePath)])-1])
		if err != nil {
			rebased[encoded] = intent
			continue
		}
		if removeIndex && itemIndex == index {
			// A tombstone belongs only to a genuinely vacant sequence slot (a
			// removal at the end). When a successor shifts into this index, that
			// live item's rebased history must own the path; retaining the removed
			// item's tombstone here creates a map-key collision and can
			// nondeterministically discard the live tag-rewrite intent.
			if !removalLeavesVacancy {
				continue
			}
			intent.target = yamlNodeSignature{}
			intent.automaticNormalization = false
			// Preserve an explicit tombstone even when this path was previously
			// created during the same edit history. A subsequent add at the same
			// index is a replacement of the original source occupant for output
			// purposes, not a fresh insertion that may reuse its custom tag.
			if !intent.origin.exists {
				intent.origin = yamlNodeSignature{exists: true}
			}
			rebased[encoded] = intent
			continue
		}
		if itemIndex > index || (!removeIndex && itemIndex >= index) {
			segments[len(sequencePath)] = indexSeg(itemIndex + delta)
			encoded = joinPath(segments)
		}
		rebased[encoded] = intent
	}
	st.nodeRewriteIntents = rebased
}

// --- Operations ---

func opTest(start *yaml.Node, tokens []ptrToken, expectRaw json.RawMessage) error {
	if len(tokens) == 0 {
		expect, err := decodeJSONValue(expectRaw)
		if err != nil {
			return fmt.Errorf("yamledit: test: %w", err)
		}
		if !deepEqual(yamlNodeToInterface(start), jsonValueToOrdered(expect)) {
			return errors.New("yamledit: test operation failed at document root")
		}
		return nil
	}
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return err
	}
	var target *yaml.Node
	if parent.Kind == yaml.SequenceNode {
		if !last.isIdx {
			return errors.New("yamledit: test: invalid array index")
		}
		if last.append {
			return errors.New("yamledit: test: '-' not allowed")
		}
		if last.index < 0 || last.index >= len(parent.Content) {
			return fmt.Errorf("yamledit: test: index %d out of bounds", last.index)
		}
		target = parent.Content[last.index]
	} else if parent.Kind == yaml.MappingNode {
		for i := len(parent.Content) - 2; i >= 0; i -= 2 {
			if isStringMappingKey(parent.Content[i], last.key) {
				target = parent.Content[i+1]
				break
			}
		}
		if target == nil {
			return fmt.Errorf("yamledit: test: key %q not found", last.key)
		}
	} else {
		return errors.New("yamledit: test: parent is not a container")
	}

	got := yamlNodeToInterface(target)
	var want interface{}
	dec := json.NewDecoder(bytes.NewReader(expectRaw))
	dec.UseNumber()
	if err := dec.Decode(&want); err != nil {
		return fmt.Errorf("yamledit: test: invalid expected value: %w", err)
	}
	want = jsonValueToOrdered(want)
	if !deepEqual(got, want) {
		return fmt.Errorf("yamledit: test operation failed: expected %v, got %v", want, got)
	}
	return nil
}
func opAdd(start *yaml.Node, st *docState, docHN *yaml.Node, basePath []ptrToken, tokens []ptrToken, raw json.RawMessage) error {
	if len(tokens) == 0 {
		return errors.New("yamledit: add: empty path not supported")
	}

	// RFC 6902 requires the target's parent to exist. Creating missing
	// intermediate objects both violates that rule and can leave mutations
	// behind when a later path segment is invalid.
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return err
	}
	destinationPath, hasDestinationPath := logicalPatchPathSegments(start, basePath, tokens)

	// decode value
	v, err := decodeJSONValue(raw)
	if err != nil {
		return err
	}
	orderedVal := jsonValueToOrdered(v)
	yval := jsonValueToYAMLNode(orderedVal)

	// ---------------------------------------------------------------------
	// Array add: parent is a sequence, last is an index or append
	// ---------------------------------------------------------------------
	if parent.Kind == yaml.SequenceNode {
		if !last.isIdx {
			return errors.New("yamledit: add: invalid array index")
		}
		if last.append {
			// Append at end
			parent.Content = append(parent.Content, yval)

			if st != nil {
				absTokens := appendPathTokens(basePath, tokens)
				// Append in ordered view
				updated, updateErr := orderedAddArray(st.ordered, absTokens, orderedVal, true)
				if updateErr != nil {
					return fmt.Errorf("yamledit: add: update ordered array: %w", updateErr)
				}
				st.ordered = updated
				if hasDestinationPath {
					recordNodeReplacementIntentLocked(st, destinationPath, nil, signatureOfYAMLNode(yval))
					markPatchSequenceScalarInsertion(st, destinationPath, orderedVal)
					recordShiftedSubtreeIntentsLocked(st, destinationPath, yval)
				}
			}
			return nil
		}

		// Insert at index
		if last.index < 0 || last.index > len(parent.Content) {
			return fmt.Errorf("yamledit: add: index %d out of bounds", last.index)
		}
		var insertionOrigin *yaml.Node
		if st != nil && hasDestinationPath {
			if encoded := joinPath(destinationPath); st.nodeRewriteIntents[encoded].origin.exists {
				insertionOrigin = parent.Content[last.index]
			}
		}
		parent.Content = append(parent.Content, nil)
		copy(parent.Content[last.index+1:], parent.Content[last.index:])
		parent.Content[last.index] = yval

		if st != nil {
			absTokens := appendPathTokens(basePath, tokens)
			// orderedAddArray handles non-append insert too (appendMode=false)
			updated, updateErr := orderedAddArray(st.ordered, absTokens, orderedVal, false)
			if updateErr != nil {
				return fmt.Errorf("yamledit: add: update ordered array: %w", updateErr)
			}
			st.ordered = updated
			if hasDestinationPath && len(destinationPath) > 0 {
				rebaseDeletionMarkersForSequence(st, destinationPath[:len(destinationPath)-1], last.index, 1, false)
				rebaseForcedScalarIntentsForSequence(st, destinationPath[:len(destinationPath)-1], last.index, 1, false)
				rebaseNodeRewriteIntentsForSequence(st, destinationPath[:len(destinationPath)-1], last.index, 1, false, false)
				recordNodeReplacementIntentLocked(st, destinationPath, insertionOrigin, signatureOfYAMLNode(yval))
				markPatchSequenceScalarInsertion(st, destinationPath, orderedVal)
				sequencePath := destinationPath[:len(destinationPath)-1]
				for itemIndex := last.index; itemIndex < len(parent.Content); itemIndex++ {
					itemPath := append(append([]string(nil), sequencePath...), indexSeg(itemIndex))
					recordShiftedSubtreeIntentsLocked(st, itemPath, parent.Content[itemIndex])
				}
			}
		}
		return nil
	}

	// ---------------------------------------------------------------------
	// Mapping add: parent is a mapping, last is a key
	// ---------------------------------------------------------------------
	if parent.Kind != yaml.MappingNode {
		return errors.New("yamledit: add: parent is not a mapping")
	}
	var oldScalar *yaml.Node
	for i := len(parent.Content) - 2; i >= 0; i -= 2 {
		if isStringMappingKey(parent.Content[i], last.key) {
			oldScalar = parent.Content[i+1]
			break
		}
	}
	if hasDestinationPath {
		markPatchScalarTagChange(st, destinationPath, oldScalar, orderedVal)
		recordNodeReplacementIntentLocked(st, destinationPath, oldScalar, signatureOfYAMLNode(yval))
	}

	// Update AST:
	// - For scalars: use upsertScalarKey (preserves "add" semantics for existing key)
	// - For complex: replace existing or append new key/value
	switch vv := orderedVal.(type) {
	case int:
		upsertScalarKey(parent, last.key, "!!int", strconv.Itoa(vv))
	case json.Number:
		tag := "!!int"
		if strings.ContainsAny(string(vv), ".eE") {
			tag = "!!float"
		}
		upsertScalarKey(parent, last.key, tag, string(vv))
		if !yamlLexemeResolvesAsTag(string(vv), tag) {
			for i := len(parent.Content) - 2; i >= 0; i -= 2 {
				if isStringMappingKey(parent.Content[i], last.key) {
					parent.Content[i+1].Style |= yaml.TaggedStyle
					break
				}
			}
		}
	case float64:
		upsertScalarKey(parent, last.key, "!!float", formatYAMLFloat(vv))
	case bool:
		if vv {
			upsertScalarKey(parent, last.key, "!!bool", "true")
		} else {
			upsertScalarKey(parent, last.key, "!!bool", "false")
		}
	case string:
		upsertScalarKey(parent, last.key, "!!str", vv)
	case nil:
		upsertScalarKey(parent, last.key, "!!null", "null")
	default:
		// Complex insert (map/array)
		replaced := false
		for i := len(parent.Content) - 2; i >= 0; i -= 2 {
			k := parent.Content[i]
			if isStringMappingKey(k, last.key) {
				old := parent.Content[i+1]
				oldKind := yaml.Kind(0)
				oldLineComment := ""
				if old != nil {
					oldKind = old.Kind
					oldLineComment = old.LineComment
					yval.Anchor = old.Anchor
					if old.Anchor != "" {
						*old = *yval
					} else {
						parent.Content[i+1] = yval
					}
				} else {
					parent.Content[i+1] = yval
				}

				// If we replaced a scalar with a complex value, move inline comment onto key line.
				if old != nil && oldKind == yaml.ScalarNode &&
					(yval.Kind == yaml.MappingNode || yval.Kind == yaml.SequenceNode) {
					if c := strings.TrimSpace(oldLineComment); c != "" {
						if parent.Content[i].LineComment == "" {
							parent.Content[i].LineComment = oldLineComment
						}
						if old != nil {
							old.LineComment = ""
						}
					}
				}

				replaced = true
				break
			}
		}
		if !replaced {
			k := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: last.key}
			parent.Content = append(parent.Content, k, yval)
		}
	}

	// Update ordered view by ptrToken path (works through sequences too).
	if st != nil {
		absTokens := appendPathTokens(basePath, tokens)

		// Upsert into ordered view (final key may be new)
		if nv, err := orderedUpsertAtPathTokens(st.ordered, absTokens, orderedVal); err == nil {
			st.ordered = nv
		} else {
			return fmt.Errorf("yamledit: add: update ordered mapping: %w", err)
		}
		if hasDestinationPath {
			clearDeletionMarkersAtOrBelow(st, destinationPath)
		}

	}

	return nil
}

func opRemove(start *yaml.Node, st *docState, docHN *yaml.Node, baseFromRoot []ptrToken, tokens []ptrToken) error {
	if len(tokens) == 0 {
		return errors.New("yamledit: remove: empty path not supported")
	}
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return err
	}
	removedPath, hasRemovedPath := logicalPatchPathSegments(start, baseFromRoot, tokens)
	if parent.Kind == yaml.SequenceNode {
		if !last.isIdx {
			return errors.New("yamledit: remove: invalid array index")
		}
		if last.append {
			return errors.New("yamledit: remove: '-' not allowed")
		}
		if last.index < 0 || last.index >= len(parent.Content) {
			return fmt.Errorf("yamledit: remove: index %d out of bounds", last.index)
		}
		target := parent.Content[last.index]
		removalLeavesVacancy := last.index == len(parent.Content)-1
		removedNodeHasIntent := hasRemovedPath && hasNodeRewriteIntentAtOrBelow(st, removedPath)
		if removalWouldBreakAlias(patchAliasScanRoot(start, docHN), target) {
			return errors.New("yamledit: remove: value defines an anchor that is still referenced")
		}
		parent.Content = append(parent.Content[:last.index], parent.Content[last.index+1:]...)
		if st != nil {
			absTokens := appendPathTokens(baseFromRoot, tokens)
			var updateErr error
			st.ordered, updateErr = orderedRemoveAtPathTokens(st.ordered, absTokens)
			if updateErr != nil {
				return fmt.Errorf("yamledit: remove: update ordered array: %w", updateErr)
			}
			if hasRemovedPath && len(removedPath) > 0 {
				rebaseDeletionMarkersForSequence(st, removedPath[:len(removedPath)-1], last.index, -1, true)
				rebaseForcedScalarIntentsForSequence(st, removedPath[:len(removedPath)-1], last.index, -1, true)
				rebaseNodeRewriteIntentsForSequence(st, removedPath[:len(removedPath)-1], last.index, -1, true, removalLeavesVacancy)
				if !removalLeavesVacancy {
					sequencePath := removedPath[:len(removedPath)-1]
					for itemIndex := last.index; itemIndex < len(parent.Content); itemIndex++ {
						itemPath := append(append([]string(nil), sequencePath...), indexSeg(itemIndex))
						recordShiftedSubtreeIntentsLocked(st, itemPath, parent.Content[itemIndex])
					}
				} else if !removedNodeHasIntent {
					recordNodeRemovalIntentLocked(st, removedPath, target)
				}
			}
		}
		return nil
	}
	if parent.Kind != yaml.MappingNode {
		return errors.New("yamledit: remove: parent is not a mapping")
	}
	found := false
	var retainedOld *yaml.Node
	targets := make([]*yaml.Node, 0, 2)
	content := make([]*yaml.Node, 0, len(parent.Content))
	for i := 0; i+1 < len(parent.Content); i += 2 {
		if isStringMappingKey(parent.Content[i], last.key) {
			found = true
			retainedOld = parent.Content[i+1]
			targets = append(targets, parent.Content[i], parent.Content[i+1])
			continue
		}
		content = append(content, parent.Content[i], parent.Content[i+1])
	}
	if !found {
		return fmt.Errorf("yamledit: remove: key %q not found", last.key)
	}
	if removalWouldBreakAlias(patchAliasScanRoot(start, docHN), targets...) {
		return errors.New("yamledit: remove: member contains an anchor that is still referenced")
	}
	if st != nil && hasRemovedPath {
		recordNodeRemovalIntentLocked(st, removedPath, retainedOld)
	}
	parent.Content = content
	if st != nil {
		absTokens := appendPathTokens(baseFromRoot, tokens)
		var updateErr error
		st.ordered, updateErr = orderedRemoveAtPathTokens(st.ordered, absTokens)
		if updateErr != nil {
			return fmt.Errorf("yamledit: remove: update ordered map: %w", updateErr)
		}
		if hasRemovedPath {
			// Use the same exact deletion-marker lifecycle as DeleteKey. Besides
			// driving source deletion, this lets a later add at the same mapping path
			// restore the removed entry's comments into the live AST exactly once.
			if st.toDelete == nil {
				st.toDelete = make(map[string]struct{})
			}
			st.toDelete[joinPath(removedPath)] = struct{}{}
			clearForcedScalarIntentAtOrBelow(st, removedPath)
		}
	}
	return nil
}

func patchAliasScanRoot(start, docHN *yaml.Node) *yaml.Node {
	if docHN != nil && docHN.Kind == yaml.DocumentNode && len(docHN.Content) > 0 {
		return docHN.Content[0]
	}
	return start
}

func opReplace(start *yaml.Node, st *docState, docHN *yaml.Node, baseFromRoot []ptrToken, tokens []ptrToken, raw json.RawMessage) error {
	if len(tokens) == 0 {
		return errors.New("yamledit: replace: empty path not supported")
	}
	// must exist
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return err
	}
	destinationPath, hasDestinationPath := logicalPatchPathSegments(start, baseFromRoot, tokens)
	v, err := decodeJSONValue(raw)
	if err != nil {
		return err
	}
	orderedVal := jsonValueToOrdered(v)
	yval := jsonValueToYAMLNode(orderedVal)

	if parent.Kind == yaml.SequenceNode {
		if !last.isIdx {
			return errors.New("yamledit: replace: invalid array index")
		}
		if last.append {
			return errors.New("yamledit: replace: '-' not allowed")
		}
		if last.index < 0 || last.index >= len(parent.Content) {
			return fmt.Errorf("yamledit: replace: index %d out of bounds", last.index)
		}
		old := parent.Content[last.index]
		reconcileReplacementPresentation(old, yval)
		if reconciled, reconcileErr := yamlNodeToOrderedValue(yval); reconcileErr == nil {
			orderedVal = reconciled
		}
		if hasDestinationPath {
			markPatchScalarTagChange(st, destinationPath, old, orderedVal)
			recordNodeReplacementIntentLocked(st, destinationPath, old, signatureOfYAMLNode(yval))
		}
		if old != nil {
			yval.HeadComment = old.HeadComment
			yval.LineComment = old.LineComment
			yval.FootComment = old.FootComment
		}
		if old != nil && old.Anchor != "" {
			yval.Anchor = old.Anchor
			*old = *yval
		} else {
			if old != nil {
				yval.Anchor = old.Anchor
			}
			parent.Content[last.index] = yval
		}
		if st != nil {
			absTokens := appendPathTokens(baseFromRoot, tokens)
			var updateErr error
			st.ordered, updateErr = orderedSetAtPathTokens(st.ordered, absTokens, orderedVal)
			if updateErr != nil {
				return fmt.Errorf("yamledit: replace: update ordered array: %w", updateErr)
			}
			if hasDestinationPath {
				clearDeletionMarkersAtOrBelow(st, destinationPath)
			}
		}
		return nil
	}
	if parent.Kind != yaml.MappingNode {
		return errors.New("yamledit: replace: parent is not a mapping")
	}
	foundKey := false
	for i := 0; i+1 < len(parent.Content); i += 2 {
		if isStringMappingKey(parent.Content[i], last.key) {
			foundKey = true
			break
		}
	}
	if !foundKey {
		return fmt.Errorf("yamledit: replace: key %q not found", last.key)
	}
	var oldScalar *yaml.Node
	for i := len(parent.Content) - 2; i >= 0; i -= 2 {
		if isStringMappingKey(parent.Content[i], last.key) {
			oldScalar = parent.Content[i+1]
			break
		}
	}
	if hasDestinationPath {
		markPatchScalarTagChange(st, destinationPath, oldScalar, orderedVal)
		recordNodeReplacementIntentLocked(st, destinationPath, oldScalar, signatureOfYAMLNode(yval))
	}
	// choose surgical replacements for scalars
	switch vv := orderedVal.(type) {
	case int:
		upsertScalarKey(parent, last.key, "!!int", strconv.Itoa(vv))
	case json.Number:
		tag := "!!int"
		if strings.ContainsAny(string(vv), ".eE") {
			tag = "!!float"
		}
		upsertScalarKey(parent, last.key, tag, string(vv))
		if !yamlLexemeResolvesAsTag(string(vv), tag) {
			for i := len(parent.Content) - 2; i >= 0; i -= 2 {
				if isStringMappingKey(parent.Content[i], last.key) {
					parent.Content[i+1].Style |= yaml.TaggedStyle
					break
				}
			}
		}
	case float64:
		upsertScalarKey(parent, last.key, "!!float", formatYAMLFloat(vv))
	case bool:
		if vv {
			upsertScalarKey(parent, last.key, "!!bool", "true")
		} else {
			upsertScalarKey(parent, last.key, "!!bool", "false")
		}
	case string:
		upsertScalarKey(parent, last.key, "!!str", vv)
	case nil:
		upsertScalarKey(parent, last.key, "!!null", "null")
	default:
		// complex (map/array)
		var oldChild *yaml.Node
		found := false
		for i := len(parent.Content) - 2; i >= 0; i -= 2 {
			if isStringMappingKey(parent.Content[i], last.key) {
				// Remember previous value before we swap it out
				oldChild = parent.Content[i+1]
				oldKind := yaml.Kind(0)
				oldLineComment := ""
				if oldChild != nil {
					reconcileReplacementPresentation(oldChild, yval)
					if reconciled, reconcileErr := yamlNodeToOrderedValue(yval); reconcileErr == nil {
						orderedVal = reconciled
					}
					oldKind = oldChild.Kind
					oldLineComment = oldChild.LineComment
					yval.Anchor = oldChild.Anchor
					if oldChild.Anchor != "" {
						*oldChild = *yval
					} else {
						parent.Content[i+1] = yval
					}
				} else {
					parent.Content[i+1] = yval
				}
				// If old value was scalar and new is complex, keep the inline comment on the *key* line
				if oldChild != nil && oldKind == yaml.ScalarNode && (yval.Kind == yaml.MappingNode || yval.Kind == yaml.SequenceNode) {
					if c := strings.TrimSpace(oldLineComment); c != "" {
						if parent.Content[i].LineComment == "" {
							parent.Content[i].LineComment = oldLineComment
						}
						// Clear the node installed in the mapping. For an unanchored
						// replacement oldChild is detached, while an anchored replacement
						// keeps that pointer in parent.Content.
						parent.Content[i+1].LineComment = ""
					}
				}
				found = true
				break
			}
		}
		if !found {
			return fmt.Errorf("yamledit: replace: key %q not found", last.key)
		}
	}
	// Ensure the ordered view also reflects scalar updates inside sequence items.
	// This handles cases where 'parent' is a mapping within an array and therefore
	// lacks a handle → path entry in subPathByHN.
	if st != nil {
		absTokens := appendPathTokens(baseFromRoot, tokens)
		nv, updateErr := orderedSetAtPathTokens(st.ordered, absTokens, orderedVal)
		if updateErr != nil {
			return fmt.Errorf("yamledit: replace: update ordered value: %w", updateErr)
		}
		st.ordered = nv
		if hasDestinationPath {
			clearDeletionMarkersAtOrBelow(st, destinationPath)
		}
	}
	return nil
}

func opMove(start *yaml.Node, st *docState, docHN *yaml.Node, baseFromRoot []ptrToken, fromToks, toToks []ptrToken) error {
	src, err := nodeAtPatchPath(start, fromToks, "move")
	if err != nil {
		return err
	}
	if ptrTokensEqual(fromToks, toToks) {
		return nil
	}
	if ptrTokensHavePrefix(toToks, fromToks) {
		return errors.New("yamledit: move: destination cannot be a child of source")
	}
	keyNode, err := mappingKeyAtPatchPath(start, fromToks)
	if err != nil {
		return err
	}
	if yamlNodeHasNonJSONMetadata(src) || yamlNodeHasNonJSONMetadata(keyNode) {
		return errors.New("yamledit: move: source contains YAML metadata that cannot be preserved")
	}
	if err := validateMoveDestination(start, fromToks, toToks); err != nil {
		return err
	}
	raw := mustMarshalJSON(yamlNodeToInterface(src))
	if raw == nil {
		return errors.New("yamledit: move: source is not JSON-compatible")
	}

	// RFC 6902 defines move as remove followed by add. The order matters when
	// moving forward within the same array because the removal shifts indices.
	if err := opRemove(start, st, docHN, baseFromRoot, fromToks); err != nil {
		return err
	}
	return opAdd(start, st, docHN, baseFromRoot, toToks, raw)
}

func mappingKeyAtPatchPath(start *yaml.Node, tokens []ptrToken) (*yaml.Node, error) {
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return nil, err
	}
	if parent.Kind != yaml.MappingNode {
		return nil, nil
	}
	for i := len(parent.Content) - 2; i >= 0; i -= 2 {
		if isStringMappingKey(parent.Content[i], last.key) {
			return parent.Content[i], nil
		}
	}
	return nil, fmt.Errorf("yamledit: move: key %q not found", last.key)
}

func validateMoveDestination(start *yaml.Node, fromToks, toToks []ptrToken) error {
	sourceParent, sourceLast, err := resolveParent(start, fromToks, false)
	if err != nil {
		return err
	}
	removedIndex := -1
	if sourceParent.Kind == yaml.SequenceNode && sourceLast.isIdx && !sourceLast.append {
		removedIndex = sourceLast.index
	}
	destinationParent, destinationLast, err := resolveParentForAddValidationAfterRemoval(start, toToks, sourceParent, removedIndex)
	if err != nil {
		return err
	}
	if destinationParent == nil || destinationParent.Kind == yaml.MappingNode {
		return nil
	}
	if destinationParent.Kind != yaml.SequenceNode {
		return errors.New("yamledit: move: destination parent is not a container")
	}
	if destinationLast.append {
		return nil
	}
	if !destinationLast.isIdx {
		return errors.New("yamledit: move: invalid destination array index")
	}
	max := len(destinationParent.Content)
	if sourceParent == destinationParent {
		max--
	}
	if destinationLast.index < 0 || destinationLast.index > max {
		return fmt.Errorf("yamledit: move: destination index %d out of bounds", destinationLast.index)
	}
	return nil
}

func resolveParentForAddValidation(start *yaml.Node, tokens []ptrToken) (*yaml.Node, ptrToken, error) {
	return resolveParentForAddValidationAfterRemoval(start, tokens, nil, -1)
}

func resolveParentForAddValidationAfterRemoval(start *yaml.Node, tokens []ptrToken, removedFrom *yaml.Node, removedIndex int) (*yaml.Node, ptrToken, error) {
	if len(tokens) == 0 {
		return nil, ptrToken{}, errors.New("yamledit: add: empty path not supported")
	}
	cur := start
	if cur.Kind == yaml.DocumentNode {
		if len(cur.Content) == 0 {
			return nil, ptrToken{}, errors.New("yamledit: document has no root")
		}
		cur = cur.Content[0]
	}
	virtualMap := false
	for i := 0; i < len(tokens)-1; i++ {
		token := tokens[i]
		if virtualMap {
			continue
		}
		switch cur.Kind {
		case yaml.MappingNode:
			if hasNonStringMappingKeyNamed(cur, token.key) {
				return nil, ptrToken{}, fmt.Errorf("yamledit: path %q collides with a non-string YAML key", token.key)
			}
			var child *yaml.Node
			for j := len(cur.Content) - 2; j >= 0; j -= 2 {
				if isStringMappingKey(cur.Content[j], token.key) {
					child = cur.Content[j+1]
					break
				}
			}
			if child == nil {
				// opAdd's documented extension creates missing mapping parents.
				virtualMap = true
				continue
			}
			cur = child
		case yaml.SequenceNode:
			index := token.index
			limit := len(cur.Content)
			if cur == removedFrom && removedIndex >= 0 {
				limit--
				if index >= removedIndex {
					index++
				}
			}
			if !token.isIdx || token.append || token.index < 0 || token.index >= limit || index >= len(cur.Content) {
				return nil, ptrToken{}, fmt.Errorf("yamledit: add: invalid array index at segment %d", i)
			}
			cur = cur.Content[index]
		default:
			return nil, ptrToken{}, fmt.Errorf("yamledit: add: cannot traverse node at segment %d", i)
		}
	}
	if virtualMap {
		return nil, tokens[len(tokens)-1], nil
	}
	last := tokens[len(tokens)-1]
	if cur != nil && cur.Kind == yaml.MappingNode && hasNonStringMappingKeyNamed(cur, last.key) {
		return nil, ptrToken{}, fmt.Errorf("yamledit: path %q collides with a non-string YAML key", last.key)
	}
	return cur, last, nil
}

func opCopy(start *yaml.Node, st *docState, docHN *yaml.Node, baseFromRoot []ptrToken, fromToks, toToks []ptrToken) error {
	// The empty JSON Pointer names the current document value. Copying that
	// value to a non-root destination is well-defined by RFC 6902: capture the
	// value before add mutates the destination. Keep nodeAtPatchPath's empty-path
	// rejection for move, whose root-source semantics are intentionally outside
	// this package's mapping-root model.
	src := start
	if len(fromToks) != 0 {
		var err error
		src, err = nodeAtPatchPath(start, fromToks, "copy")
		if err != nil {
			return err
		}
	}
	if yamlNodeHasNonJSONType(src) {
		return errors.New("yamledit: copy: source is not JSON-compatible")
	}
	raw := mustMarshalJSON(yamlNodeToInterface(src))
	if raw == nil {
		return errors.New("yamledit: copy: source is not JSON-compatible")
	}
	return opAdd(start, st, docHN, baseFromRoot, toToks, raw)
}

func nodeAtPatchPath(start *yaml.Node, tokens []ptrToken, op string) (*yaml.Node, error) {
	if len(tokens) == 0 {
		return nil, fmt.Errorf("yamledit: %s: empty 'from' path not supported", op)
	}
	parent, last, err := resolveParent(start, tokens, false)
	if err != nil {
		return nil, err
	}
	if parent.Kind == yaml.SequenceNode {
		if !last.isIdx || last.append || last.index < 0 || last.index >= len(parent.Content) {
			return nil, fmt.Errorf("yamledit: %s: invalid 'from' index", op)
		}
		return parent.Content[last.index], nil
	}
	if parent.Kind != yaml.MappingNode {
		return nil, fmt.Errorf("yamledit: %s: invalid 'from' parent", op)
	}
	for i := len(parent.Content) - 2; i >= 0; i -= 2 {
		if isStringMappingKey(parent.Content[i], last.key) {
			return parent.Content[i+1], nil
		}
	}
	return nil, fmt.Errorf("yamledit: %s: key %q not found", op, last.key)
}

func ptrTokensEqual(a, b []ptrToken) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].key != b[i].key || a[i].isIdx != b[i].isIdx || a[i].index != b[i].index || a[i].append != b[i].append {
			return false
		}
	}
	return true
}

func ptrTokensHavePrefix(path, prefix []ptrToken) bool {
	return len(path) > len(prefix) && ptrTokensEqual(path[:len(prefix)], prefix)
}

func mustMarshalJSON(v interface{}) json.RawMessage {
	b, err := json.Marshal(v)
	if err != nil {
		return nil
	}
	return b
}

func deepEqual(a, b interface{}) bool {
	a = toPlain(a)
	b = toPlain(b)
	if an, ok := canonicalDecimal(a); ok {
		bn, bok := canonicalDecimal(b)
		return bok && an == bn
	}
	switch av := a.(type) {
	case map[string]interface{}:
		bv, ok := b.(map[string]interface{})
		if !ok || len(av) != len(bv) {
			return false
		}
		for key, value := range av {
			other, exists := bv[key]
			if !exists || !deepEqual(value, other) {
				return false
			}
		}
		return true
	case []interface{}:
		bv, ok := b.([]interface{})
		if !ok || len(av) != len(bv) {
			return false
		}
		for i := range av {
			if !deepEqual(av[i], bv[i]) {
				return false
			}
		}
		return true
	default:
		return reflect.DeepEqual(a, b)
	}
}

type normalizedDecimal struct {
	negative bool
	digits   string
	scale    string
}

func canonicalDecimal(v interface{}) (normalizedDecimal, bool) {
	var decimal string
	switch n := v.(type) {
	case json.Number:
		decimal = string(n)
	case int:
		decimal = strconv.Itoa(n)
	case int8:
		decimal = strconv.FormatInt(int64(n), 10)
	case int16:
		decimal = strconv.FormatInt(int64(n), 10)
	case int32:
		decimal = strconv.FormatInt(int64(n), 10)
	case int64:
		decimal = strconv.FormatInt(n, 10)
	case uint:
		decimal = strconv.FormatUint(uint64(n), 10)
	case uint8:
		decimal = strconv.FormatUint(uint64(n), 10)
	case uint16:
		decimal = strconv.FormatUint(uint64(n), 10)
	case uint32:
		decimal = strconv.FormatUint(uint64(n), 10)
	case uint64:
		decimal = strconv.FormatUint(n, 10)
	case float32:
		decimal = strconv.FormatFloat(float64(n), 'g', -1, 32)
	case float64:
		decimal = strconv.FormatFloat(n, 'g', -1, 64)
	default:
		return normalizedDecimal{}, false
	}
	return normalizeDecimalNumber(decimal)
}

func normalizeDecimalNumber(s string) (normalizedDecimal, bool) {
	if s == "" {
		return normalizedDecimal{}, false
	}
	negative := false
	if s[0] == '-' || s[0] == '+' {
		negative = s[0] == '-'
		s = s[1:]
	}
	var exponent big.Int
	if pos := strings.IndexAny(s, "eE"); pos >= 0 {
		if _, ok := exponent.SetString(s[pos+1:], 10); !ok {
			return normalizedDecimal{}, false
		}
		s = s[:pos]
	}
	var fractionDigits int
	if dot := strings.IndexByte(s, '.'); dot >= 0 {
		fractionDigits = len(s) - dot - 1
		s = s[:dot] + s[dot+1:]
	}
	if s == "" {
		return normalizedDecimal{}, false
	}
	for _, digit := range s {
		if digit < '0' || digit > '9' {
			return normalizedDecimal{}, false
		}
	}
	s = strings.TrimLeft(s, "0")
	if s == "" {
		return normalizedDecimal{digits: "0", scale: "0"}, true
	}
	trailing := len(s) - len(strings.TrimRight(s, "0"))
	if trailing > 0 {
		s = s[:len(s)-trailing]
	}
	// JSON permits an exponent with any number of digits. Keep the normalized
	// decimal scale at arbitrary precision as well, otherwise mathematically
	// equal inputs stop comparing equal at the int64 exponent boundary.
	var scale, adjustment big.Int
	scale.Set(&exponent)
	adjustment.SetInt64(int64(fractionDigits))
	scale.Sub(&scale, &adjustment)
	adjustment.SetInt64(int64(trailing))
	scale.Add(&scale, &adjustment)
	return normalizedDecimal{negative: negative, digits: s, scale: scale.String()}, true
}

// --- Ordered updates for arrays (best-effort for fallback encoder) ---

func appendPathTokens(prefix []ptrToken, toks []ptrToken) []ptrToken {
	out := make([]ptrToken, 0, len(prefix)+len(toks))
	out = append(out, prefix...)
	out = append(out, toks...)
	return out
}

// Walk st.ordered and add into an array location.
func orderedAddArray(ms gyaml.MapSlice, path []ptrToken, val interface{}, appendMode bool) (gyaml.MapSlice, error) {
	ov := jsonValueToOrdered(val)
	nv, err := orderedArrayEdit(ms, path, func(cur []interface{}) ([]interface{}, error) {
		if appendMode {
			return append(cur, ov), nil
		}
		// find index from last token
		last := path[len(path)-1]
		if last.index < 0 || last.index > len(cur) {
			return nil, fmt.Errorf("index %d out of bounds", last.index)
		}
		cur = append(cur, nil)
		copy(cur[last.index+1:], cur[last.index:])
		cur[last.index] = ov
		return cur, nil
	})
	if err != nil {
		return ms, err
	}
	return nv, nil
}

func orderedReplaceArray(ms gyaml.MapSlice, path []ptrToken, val interface{}) (gyaml.MapSlice, error) {
	ov := jsonValueToOrdered(val)
	return orderedArrayEdit(ms, path, func(cur []interface{}) ([]interface{}, error) {
		last := path[len(path)-1]
		if last.index < 0 || last.index >= len(cur) {
			return nil, fmt.Errorf("index %d out of bounds", last.index)
		}
		cur[last.index] = ov
		return cur, nil
	})
}

func orderedRemoveArray(ms gyaml.MapSlice, path []ptrToken) (gyaml.MapSlice, error) {
	return orderedArrayEdit(ms, path, func(cur []interface{}) ([]interface{}, error) {
		last := path[len(path)-1]
		if last.index < 0 || last.index >= len(cur) {
			return nil, fmt.Errorf("index %d out of bounds", last.index)
		}
		return append(cur[:last.index], cur[last.index+1:]...), nil
	})
}

// orderedRemoveAtPathTokens removes either a mapping member or a sequence item,
// interpreting numeric tokens according to the container being traversed.
func orderedRemoveAtPathTokens(ms gyaml.MapSlice, path []ptrToken) (gyaml.MapSlice, error) {
	if len(path) == 0 {
		return ms, errors.New("orderedRemoveAtPath: empty path")
	}

	var recur func(interface{}, int) (interface{}, error)
	recur = func(cur interface{}, depth int) (interface{}, error) {
		t := path[depth]
		switch v := cur.(type) {
		case gyaml.MapSlice:
			found := -1
			for i := len(v) - 1; i >= 0; i-- {
				if keyEquals(v[i].Key, t.key) {
					found = i
					break
				}
			}
			if found < 0 {
				return nil, fmt.Errorf("orderedRemoveAtPath: key %q not found", t.key)
			}
			if depth == len(path)-1 {
				out := make(gyaml.MapSlice, 0, len(v)-1)
				for _, item := range v {
					if !keyEquals(item.Key, t.key) {
						out = append(out, item)
					}
				}
				return out, nil
			}
			next, err := recur(v[found].Value, depth+1)
			if err != nil {
				return nil, err
			}
			v[found].Value = next
			return v, nil

		case map[string]interface{}:
			child, ok := v[t.key]
			if !ok {
				return nil, fmt.Errorf("orderedRemoveAtPath: key %q not found", t.key)
			}
			if depth == len(path)-1 {
				delete(v, t.key)
				return v, nil
			}
			next, err := recur(child, depth+1)
			if err != nil {
				return nil, err
			}
			v[t.key] = next
			return v, nil

		case []interface{}:
			if !t.isIdx || t.append {
				return nil, fmt.Errorf("orderedRemoveAtPath: invalid array index at segment %d", depth)
			}
			if t.index < 0 || t.index >= len(v) {
				return nil, fmt.Errorf("orderedRemoveAtPath: index %d out of bounds", t.index)
			}
			if depth == len(path)-1 {
				return append(v[:t.index], v[t.index+1:]...), nil
			}
			next, err := recur(v[t.index], depth+1)
			if err != nil {
				return nil, err
			}
			v[t.index] = next
			return v, nil
		default:
			return nil, fmt.Errorf("orderedRemoveAtPath: unexpected type at segment %d (%T)", depth, cur)
		}
	}

	out, err := recur(ms, 0)
	if err != nil {
		return ms, err
	}
	res, ok := out.(gyaml.MapSlice)
	if !ok {
		return ms, fmt.Errorf("orderedRemoveAtPath: root type changed (%T)", out)
	}
	return res, nil
}

// orderedArrayEdit navigates to the []interface{} pointed by path (last segment is an index/appender)
// and applies 'edit', returning an updated MapSlice.
func orderedArrayEdit(ms gyaml.MapSlice, path []ptrToken, edit func([]interface{}) ([]interface{}, error)) (gyaml.MapSlice, error) {
	var recur func(cur interface{}, depth int) (interface{}, error)
	recur = func(cur interface{}, depth int) (interface{}, error) {
		if depth >= len(path) {
			return cur, nil
		}
		t := path[depth]
		switch v := cur.(type) {
		case gyaml.MapSlice:
			// locate key
			found := -1
			for i := len(v) - 1; i >= 0; i-- {
				if keyEquals(v[i].Key, t.key) {
					found = i
					break
				}
			}
			if found < 0 {
				return nil, fmt.Errorf("path key %q not found in ordered map", t.key)
			}
			next, err := recur(v[found].Value, depth+1)
			if err != nil {
				return nil, err
			}
			v[found].Value = next
			return v, nil
		case []interface{}:
			if !t.isIdx {
				return nil, fmt.Errorf("expected index at segment %d", depth)
			}
			if depth == len(path)-1 {
				// apply edit
				return edit(v)
			}
			if t.append {
				return nil, fmt.Errorf("'-' only valid at the last segment")
			}
			if t.index < 0 || t.index >= len(v) {
				return nil, fmt.Errorf("index %d out of bounds", t.index)
			}
			next, err := recur(v[t.index], depth+1)
			if err != nil {
				return nil, err
			}
			v[t.index] = next
			return v, nil
		default:
			return nil, fmt.Errorf("unexpected type at segment %d", depth)
		}
	}
	out, err := recur(ms, 0)
	if err != nil {
		return ms, err
	}
	res, _ := out.(gyaml.MapSlice)
	return res, nil
}

// orderedSetAtPathTokens sets a scalar value at the path indicated by tokens.
// The final token MUST be a mapping key (not an index). Intermediate segments
// may traverse through arrays (sequence indices) and mappings.
func orderedSetAtPathTokens(ms gyaml.MapSlice, path []ptrToken, val interface{}) (gyaml.MapSlice, error) {
	ov := jsonValueToOrdered(val)

	var recur func(cur interface{}, depth int) (interface{}, error)
	recur = func(cur interface{}, depth int) (interface{}, error) {
		if depth >= len(path) {
			return nil, fmt.Errorf("orderedSetAtPath: empty path at depth %d", depth)
		}
		t := path[depth]
		switch v := cur.(type) {
		case gyaml.MapSlice:
			// locate key
			found := -1
			for i := len(v) - 1; i >= 0; i-- {
				if keyEquals(v[i].Key, t.key) {
					found = i
					break
				}
			}
			if found < 0 {
				return nil, fmt.Errorf("orderedSetAtPath: path key %q not found", t.key)
			}
			if depth == len(path)-1 {
				// final segment is a key → set its scalar value
				v[found].Value = ov
				return v, nil
			}
			next, err := recur(v[found].Value, depth+1)
			if err != nil {
				return nil, err
			}
			v[found].Value = next
			return v, nil

		case map[string]interface{}:
			// Handle native map as well (can occur inside []interface{}).
			child, ok := v[t.key]
			if !ok {
				return nil, fmt.Errorf("orderedSetAtPath: path key %q not found", t.key)
			}
			if depth == len(path)-1 {
				v[t.key] = ov
				return v, nil
			}
			next, err := recur(child, depth+1)
			if err != nil {
				return nil, err
			}
			v[t.key] = next
			return v, nil

		case []interface{}:
			if !t.isIdx {
				return nil, fmt.Errorf("orderedSetAtPath: expected index at segment %d", depth)
			}
			if t.append {
				return nil, fmt.Errorf("orderedSetAtPath: '-' not valid for set")
			}
			if t.index < 0 || t.index >= len(v) {
				return nil, fmt.Errorf("orderedSetAtPath: index %d out of bounds", t.index)
			}
			if depth == len(path)-1 {
				// Not used for this test, but support setting entire element if addressed directly.
				v[t.index] = ov
				return v, nil
			}
			next, err := recur(v[t.index], depth+1)
			if err != nil {
				return nil, err
			}
			v[t.index] = next
			return v, nil
		default:
			return nil, fmt.Errorf("orderedSetAtPath: unexpected type at segment %d (%T)", depth, v)
		}
	}
	out, err := recur(ms, 0)
	if err != nil {
		return ms, err
	}
	res, _ := out.(gyaml.MapSlice)
	return res, nil
}

// orderedUpsertAtPathTokens sets a value at the path indicated by tokens.
// Unlike orderedSetAtPathTokens, it will CREATE the final mapping key if missing.
// Intermediate missing mapping keys are created as empty maps (gyaml.MapSlice{}),
// but we do NOT auto-create arrays (JSON Patch "add" can't conjure arrays either).
func orderedUpsertAtPathTokens(ms gyaml.MapSlice, path []ptrToken, val interface{}) (gyaml.MapSlice, error) {
	ov := jsonValueToOrdered(val)

	var recur func(cur interface{}, depth int) (interface{}, error)
	recur = func(cur interface{}, depth int) (interface{}, error) {
		if depth >= len(path) {
			return cur, nil
		}
		t := path[depth]

		switch v := cur.(type) {
		case gyaml.MapSlice:
			found := -1
			for i := len(v) - 1; i >= 0; i-- {
				if keyEquals(v[i].Key, t.key) {
					found = i
					break
				}
			}

			// Final segment must be a key: set or append.
			if depth == len(path)-1 {
				if found >= 0 {
					v[found].Value = ov
					return v, nil
				}
				v = append(v, gyaml.MapItem{Key: t.key, Value: ov})
				return v, nil
			}

			// Intermediate segment: ensure container exists.
			if found < 0 {
				v = append(v, gyaml.MapItem{Key: t.key, Value: gyaml.MapSlice{}})
				found = len(v) - 1
			}

			nextVal, err := recur(v[found].Value, depth+1)
			if err != nil {
				return nil, err
			}
			v[found].Value = nextVal
			return v, nil

		case map[string]interface{}:
			if depth == len(path)-1 {
				v[t.key] = ov
				return v, nil
			}
			child, ok := v[t.key]
			if !ok {
				child = map[string]interface{}{}
				v[t.key] = child
			}
			nextVal, err := recur(child, depth+1)
			if err != nil {
				return nil, err
			}
			v[t.key] = nextVal
			return v, nil

		case []interface{}:
			if !t.isIdx || t.append {
				return nil, fmt.Errorf("orderedUpsertAtPath: expected index at segment %d", depth)
			}
			if t.index < 0 || t.index >= len(v) {
				return nil, fmt.Errorf("orderedUpsertAtPath: index %d out of bounds", t.index)
			}
			if depth == len(path)-1 {
				v[t.index] = ov
				return v, nil
			}
			nextVal, err := recur(v[t.index], depth+1)
			if err != nil {
				return nil, err
			}
			v[t.index] = nextVal
			return v, nil

		default:
			return nil, fmt.Errorf("orderedUpsertAtPath: unexpected type at segment %d (%T)", depth, v)
		}
	}

	out, err := recur(ms, 0)
	if err != nil {
		return ms, err
	}
	res, ok := out.(gyaml.MapSlice)
	if !ok {
		return ms, fmt.Errorf("orderedUpsertAtPath: root type changed (%T)", out)
	}
	return res, nil
}

// setOrderedAtPath updates an ordered MapSlice using a ptrToken path
// (keys + indices). It’s a thin wrapper around orderedSetAtPathTokens so
// callers that already operate on ptrToken paths (like normalizeImplicitMaps)
// can reuse the same machinery.
func setOrderedAtPath(ms gyaml.MapSlice, path []ptrToken, val interface{}) (gyaml.MapSlice, error) {
	return orderedSetAtPathTokens(ms, path, val)
}
