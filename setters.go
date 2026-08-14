package yamledit

import (
	"encoding/json"
	"fmt"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"weak"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// SetValueOptions controls how generic YAML value writers handle map ordering and omissions.
type SetValueOptions struct {
	DeleteEmptyStrings bool
	SortKeys           bool
}

// EnsurePath returns a mapping node for the nested keys (creates when missing).
// It accepts either a root DocumentNode or a MappingNode as the starting point.
func EnsurePath(node *yaml.Node, first string, rest ...string) *yaml.Node {
	if node == nil {
		return nil
	}

	keys := append([]string{first}, rest...)

	// Resolve state + starting mapping node without reading mutable node fields
	// before taking the owning document lock.
	var (
		st         *docState
		startMap   *yaml.Node
		baseTokens []ptrToken // exact path, including sequence indices
	)
	if owner, doc, isDocument, registered := findRegisteredNodeOwner(node); registered {
		st = owner
		st.mu.Lock()
		defer st.mu.Unlock()
		noteDirectASTMutationLocked(st)
		var err error
		startMap, baseTokens, err = resolveRegisteredStartLocked(node, st, doc, isDocument)
		if err != nil {
			return nil
		}
	} else {
		switch node.Kind {
		case yaml.DocumentNode:
			if len(node.Content) == 0 || node.Content[0].Kind != yaml.MappingNode {
				return nil
			}
			startMap = node.Content[0]
		case yaml.MappingNode:
			startMap = node
		default:
			return nil
		}
	}

	// Walk/construct from startMap
	cur := startMap
	curTokens := append([]ptrToken(nil), baseTokens...)
	for _, k := range keys {
		if hasNonStringMappingKeyNamed(cur, k) {
			return nil
		}
		var found *yaml.Node
		var keyNode *yaml.Node
		for i := len(cur.Content) - 2; i >= 0; i -= 2 {
			if isStringMappingKey(cur.Content[i], k) {
				keyNode = cur.Content[i]
				found = cur.Content[i+1]
				break
			}
		}

		segmentChanged := false
		nextTokens := append(append([]ptrToken(nil), curTokens...), ptrToken{key: k})
		if found == nil {
			if st != nil {
				recordNodeReplacementIntentLocked(st, tokenPathSegments(nextTokens), nil, yamlNodeSignature{kind: yaml.MappingNode, tag: "!!map", exists: true})
			}
			key := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: k}
			val := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			cur.Content = append(cur.Content, key, val)
			keyNode = key
			found = val
			segmentChanged = true
		}
		if found.Kind != yaml.MappingNode {
			if st != nil {
				recordNodeReplacementIntentLocked(st, tokenPathSegments(nextTokens), found, yamlNodeSignature{kind: yaml.MappingNode, tag: "!!map", exists: true})
			}
			// Preserve comments, but keep the old inline comment on the *key* line
			oldHead, oldLine, oldFoot, oldAnchor := found.HeadComment, found.LineComment, found.FootComment, found.Anchor
			repl := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			repl.HeadComment, repl.FootComment, repl.Anchor = oldHead, oldFoot, oldAnchor
			// Clear the inline comment on the value; attach to key instead
			if keyNode != nil && oldLine != "" {
				// Only assign if the key doesn't already have an inline comment
				if keyNode.LineComment == "" {
					keyNode.LineComment = oldLine
				}
			}
			*found = *repl
			segmentChanged = true
		}
		cur = found
		curTokens = nextTokens

		// Keep handle → path mapping up to date for new/converted nodes
		if st != nil {
			if segmentChanged {
				// A delete marker describes the old subtree at this path. Creating or
				// replacing that subtree invalidates the marker and every marker below
				// it. Do not clear markers merely while traversing an existing mapping:
				// an unrelated child deletion must remain pending.
				clearDeletionMarkersAtOrBelow(st, tokenPathSegments(curTokens))
			}
			if keyPath, ok := mappingOnlyTokenPath(curTokens); ok {
				st.subPathByHN[weak.Make(cur)] = keyPath
			}
		}
	}

	// Keep ordered (logical) view in sync
	if st != nil {
		if updated, err := orderedEnsureMapPath(st.ordered, curTokens); err == nil {
			st.ordered = updated
		}
		recordExpectedASTLocked(st)
	}

	return cur
}

func mappingOnlyTokenPath(path []ptrToken) ([]string, bool) {
	out := make([]string, 0, len(path))
	for _, token := range path {
		if token.isIdx {
			return nil, false
		}
		out = append(out, token.key)
	}
	return out, true
}

func orderedEnsureMapPath(ms gyaml.MapSlice, path []ptrToken) (gyaml.MapSlice, error) {
	if len(path) == 0 {
		return ms, nil
	}
	var recur func(interface{}, int) (interface{}, error)
	recur = func(cur interface{}, depth int) (interface{}, error) {
		token := path[depth]
		switch value := cur.(type) {
		case gyaml.MapSlice:
			found := -1
			for i := range value {
				if keyEquals(value[i].Key, token.key) {
					found = i
				}
			}
			if found < 0 {
				value = append(value, gyaml.MapItem{Key: token.key, Value: gyaml.MapSlice{}})
				found = len(value) - 1
			}
			if depth == len(path)-1 {
				if _, ok := value[found].Value.(gyaml.MapSlice); !ok {
					value[found].Value = gyaml.MapSlice{}
				}
				return value, nil
			}
			next, err := recur(value[found].Value, depth+1)
			if err != nil {
				return nil, err
			}
			value[found].Value = next
			return value, nil

		case []interface{}:
			if !token.isIdx || token.append || token.index < 0 || token.index >= len(value) {
				return nil, fmt.Errorf("orderedEnsureMapPath: invalid index at segment %d", depth)
			}
			next, err := recur(value[token.index], depth+1)
			if err != nil {
				return nil, err
			}
			value[token.index] = next
			return value, nil
		default:
			return nil, fmt.Errorf("orderedEnsureMapPath: cannot traverse %T at segment %d", cur, depth)
		}
	}

	out, err := recur(ms, 0)
	if err != nil {
		return ms, err
	}
	updated, ok := out.(gyaml.MapSlice)
	if !ok {
		return ms, fmt.Errorf("orderedEnsureMapPath: root changed to %T", out)
	}
	return updated, nil
}

// recordExpectedASTLocked records the tree state produced by a public mutator.
// The caller must hold st.mu for writing. Keeping this separate from the ordered
// shadow lets Marshal distinguish those intentional edits from callers changing
// yaml.Node fields directly (including comments, tags, styles, and aliases).
func recordExpectedASTLocked(st *docState) {
	if st == nil {
		return
	}
	if doc := st.root(); doc != nil {
		st.expectedAST = cloneYAMLNodeGraph(doc)
	}
}

func setForcedScalarIntentLocked(st *docState, path []string, tag string) {
	if st == nil || len(path) == 0 {
		return
	}
	if st.forceScalarRewrite == nil {
		st.forceScalarRewrite = make(map[string]struct{})
	}
	if st.forceScalarTags == nil {
		st.forceScalarTags = make(map[string]string)
	}
	encoded := joinPath(path)
	st.forceScalarRewrite[encoded] = struct{}{}
	st.forceScalarTags[encoded] = tag
}

func noteDirectASTMutationLocked(st *docState) {
	if st == nil || st.directASTDirty {
		return
	}
	if doc := st.root(); doc != nil && !yamlNodeGraphEqual(doc, st.expectedAST) {
		st.directASTDirty = true
	}
}

// setScalarNode updates a scalar node while preserving existing comments.
func setScalarNode(n *yaml.Node, tag, val string) {
	head, line, foot := n.HeadComment, n.LineComment, n.FootComment
	n.Kind = yaml.ScalarNode
	n.Tag = tag
	n.Value = val
	n.Style = 0
	n.Content = nil
	n.Alias = nil
	n.HeadComment, n.LineComment, n.FootComment = head, line, foot
}

// upsertScalarKey rewrites existing scalar values for key (all occurrences) or appends a new pair.
func upsertScalarKey(mapNode *yaml.Node, key, tag, val string) {
	updated := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		if isStringMappingKey(k, key) {
			if mapNode.Content[i+1] == nil {
				// Public yaml.Node values are mutable, so callers can hand a setter a
				// malformed pair with a nil value node. Repair the exact pair instead
				// of dereferencing nil; other malformed content remains untouched and
				// will still be rejected by Marshal.
				mapNode.Content[i+1] = &yaml.Node{Kind: yaml.ScalarNode, Tag: tag, Value: val}
			} else {
				oldKind := mapNode.Content[i+1].Kind
				setScalarNode(mapNode.Content[i+1], tag, val)
				if (oldKind == yaml.MappingNode || oldKind == yaml.SequenceNode) && k.LineComment != "" {
					if mapNode.Content[i+1].LineComment == "" {
						mapNode.Content[i+1].LineComment = k.LineComment
					}
					k.LineComment = ""
				}
			}
			updated = true
		}
	}
	if updated {
		return
	}
	keyNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}
	valNode := &yaml.Node{Kind: yaml.ScalarNode, Tag: tag, Value: val}
	mapNode.Content = append(mapNode.Content, keyNode, valNode)
}

// setScalarValue centralizes scalar writes, keeping docState/ordered map in sync.
func setScalarValue(
	mapNode *yaml.Node,
	key string,
	tag string,
	val string,
	logicalValue any,
	updateOrdered func(ms gyaml.MapSlice, path []string, key string) gyaml.MapSlice,
) {
	if mapNode == nil {
		return
	}

	st, docHN, isDocument, registered := findRegisteredNodeOwner(mapNode)
	var mapPathTokens []ptrToken
	if registered {
		if isDocument {
			return
		}
		st.mu.Lock()
		defer st.mu.Unlock()
		noteDirectASTMutationLocked(st)
		root := st.root()
		if root == nil || root != docHN || len(root.Content) == 0 {
			return
		}
		var reachable bool
		mapPathTokens, reachable = addressableTokenPathToNode(root.Content[0], mapNode)
		if !reachable || mapNode.Kind != yaml.MappingNode {
			return
		}
	} else {
		st = nil
		docHN = nil
		if mapNode.Kind != yaml.MappingNode {
			return
		}
	}
	if hasNonStringMappingKeyNamed(mapNode, key) {
		return
	}

	forceRewrite := false
	var oldNode *yaml.Node
	for i := len(mapNode.Content) - 2; i >= 0; i -= 2 {
		if isStringMappingKey(mapNode.Content[i], key) {
			oldNode = mapNode.Content[i+1]
			if oldNode != nil && oldNode.Kind == yaml.ScalarNode && oldNode.Tag != tag {
				forceRewrite = true
			}
			break
		}
	}
	if st != nil {
		fullPath := append(tokenPathSegments(mapPathTokens), key)
		recordNodeReplacementIntentLocked(st, fullPath, oldNode, yamlNodeSignature{kind: yaml.ScalarNode, tag: tag, exists: true})
	}

	// Always update the yaml.v3 AST first.
	upsertScalarKey(mapNode, key, tag, val)

	if st == nil {
		return
	}

	// If this mapping node is indexed as a mapping (i.e. reachable by keys),
	// update the ordered MapSlice through that mapping path.
	mapRef := weak.Make(mapNode)
	if _, ok := st.subPathByHN[mapRef]; !ok && docHN != nil && len(docHN.Content) > 0 {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	if path, ok := st.subPathByHN[mapRef]; ok {
		st.ordered = updateOrdered(st.ordered, path, key)
		fullPath := append(append([]string(nil), path...), key)
		clearDeletionMarkersAtOrBelow(st, fullPath)
		if forceRewrite {
			setForcedScalarIntentLocked(st, fullPath, tag)
		}
		recordExpectedASTLocked(st)
		return
	}

	// Mapping nodes inside sequences need an index-aware path. Resolve the
	// pointer directly from the locked AST so newly inserted fields (which have
	// no source Line/Column) can still update the ordered shadow correctly.
	if root := st.root(); root != nil && len(root.Content) > 0 {
		if base, ok := addressableTokenPathToNode(root.Content[0], mapNode); ok {
			full := append(append([]ptrToken(nil), base...), ptrToken{key: key})
			if updated, err := orderedUpsertAtPathTokens(st.ordered, full, logicalValue); err == nil {
				st.ordered = updated
				fullPath := append(tokenPathSegments(base), key)
				clearDeletionMarkersAtOrBelow(st, fullPath)
				if forceRewrite {
					setForcedScalarIntentLocked(st, fullPath, tag)
				}
				recordExpectedASTLocked(st)
				return
			}
		}
	}

	// Otherwise, this mapping node is most likely an item inside a sequence.
	// In that case, we don't have a mapping-based path; instead, we locate the
	// scalar occurrence by its byte offset and update the ordered view using a
	// ptrToken path derived from valueOccByPathKey.
	if updateScalarInSequenceOrdered(st, mapNode, key, logicalValue) {
		// sequence items are not tracked in toDelete, so nothing to clear there
		recordExpectedASTLocked(st)
		return
	}

	// The AST remains updated even when this source-offset fallback cannot
	// reconcile the ordered shadow. Marshal compares it with the expected live
	// tree and either finds a safe scoped rewrite or returns an error.
	recordExpectedASTLocked(st)
}

// updateScalarInSequenceOrdered updates st.ordered for a scalar that lives inside
// a mapping which itself is an item of a sequence. It discovers the logical
// ptrToken path by matching the scalar node's byte position against
// valueOccByPathKey entries and then calls orderedSetAtPathTokens.
func updateScalarInSequenceOrdered(st *docState, mapNode *yaml.Node, key string, logicalValue any) bool {
	if st == nil || mapNode == nil || mapNode.Kind != yaml.MappingNode {
		return false
	}

	// Find the scalar node we just updated for this key.
	var valNode *yaml.Node
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		v := mapNode.Content[i+1]
		if isStringMappingKey(k, key) {
			valNode = v
			break
		}
	}
	if valNode == nil || valNode.Line <= 0 || valNode.Column <= 0 {
		return false
	}

	valStart := scalarValueOffset(st.original, st.lineOffsets, valNode)
	if valStart < 0 || valStart >= len(st.original) {
		return false
	}

	// Find the pathKey whose last occurrence has this valStart; this ties the
	// scalar back to a logical path like "list\x00[0]\x00name".
	var targetPK string
	for pk, occs := range st.valueOccByPathKey {
		for _, occ := range occs {
			if occ.valStart == valStart {
				targetPK = pk
				break
			}
		}
		if targetPK != "" {
			break
		}
	}
	if targetPK == "" {
		return false
	}

	segs, ok := splitJoinedPath(targetPK)
	if !ok || len(segs) == 0 {
		return false
	}
	last := segs[len(segs)-1]
	// For mapping fields inside sequence items, the last segment should be the key.
	if last != key {
		return false
	}

	// Build ptrToken path: mapping keys + sequence indices + final mapping key.
	pathSegs := segs[:len(segs)-1]
	toks := make([]ptrToken, 0, len(pathSegs)+1)
	for _, s := range pathSegs {
		if len(s) > 2 && s[0] == '[' && s[len(s)-1] == ']' {
			// "[idx]" -> array index
			i, err := strconv.Atoi(s[1 : len(s)-1])
			if err != nil {
				return false
			}
			toks = append(toks, ptrToken{isIdx: true, index: i})
		} else {
			toks = append(toks, ptrToken{key: s})
		}
	}
	toks = append(toks, ptrToken{key: key})

	newOrdered, err := orderedSetAtPathTokens(st.ordered, toks, logicalValue)
	if err != nil {
		return false
	}
	st.ordered = newOrdered
	return true
}

// SetScalarInt sets an integer value under the mapping node.
func SetScalarInt(mapNode *yaml.Node, key string, value int) {
	valStr := fmt.Sprintf("%d", value)
	setScalarValue(mapNode, key, "!!int", valStr, value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setIntAtPath(ms, path, k, value)
	})
}

func setScalarInt64(mapNode *yaml.Node, key string, value int64) {
	valStr := strconv.FormatInt(value, 10)
	setScalarValue(mapNode, key, "!!int", valStr, value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setAnyAtPath(ms, path, k, value)
	})
}

func setScalarUint64(mapNode *yaml.Node, key string, value uint64) {
	valStr := strconv.FormatUint(value, 10)
	setScalarValue(mapNode, key, "!!int", valStr, value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setAnyAtPath(ms, path, k, value)
	})
}

// SetScalarString sets a string value under the mapping node.
func SetScalarString(mapNode *yaml.Node, key, value string) {
	setScalarValue(mapNode, key, "!!str", value, value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setStringAtPath(ms, path, k, value)
	})
}

// SetScalarBool sets a boolean value under the mapping node.
// Byte-surgical replacement writes canonical YAML booleans ("true"/"false").
func SetScalarBool(mapNode *yaml.Node, key string, value bool) {
	valStr := "false"
	if value {
		valStr = "true"
	}

	setScalarValue(mapNode, key, "!!bool", valStr, value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setBoolAtPath(ms, path, k, value)
	})
}

// SetScalarFloat sets a float value under the mapping node.
func SetScalarFloat(mapNode *yaml.Node, key string, value float64) {
	valStr := formatYAMLFloat(value)
	setScalarValue(mapNode, key, "!!float", valStr, value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setFloatAtPath(ms, path, k, value)
	})
}

// setScalarJSONNumber preserves both the exact JSON number lexeme and its YAML
// numeric category. json.Number is publicly constructible, so invalid values
// are handled by SetValue as ordinary strings before reaching this helper.
func setScalarJSONNumber(mapNode *yaml.Node, key string, value json.Number) {
	tag, _ := scalarYAMLTag(value)
	setScalarValue(mapNode, key, tag, value.String(), value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setAnyAtPath(ms, path, k, value)
	})
}

// SetScalarNull sets a null value (!!null) under the mapping node.
func SetScalarNull(mapNode *yaml.Node, key string) {
	setScalarValue(mapNode, key, "!!null", "null", nil, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setNullAtPath(ms, path, k)
	})
}

// SetMapValues writes arbitrary map values into a YAML mapping node.
func SetMapValues(mapNode *yaml.Node, fields map[string]any, opts SetValueOptions) {
	if mapNode == nil {
		return
	}
	keys := make([]string, 0, len(fields))
	for key := range fields {
		keys = append(keys, key)
	}
	if opts.SortKeys {
		sort.Strings(keys)
	}
	for _, key := range keys {
		SetValue(mapNode, key, fields[key], opts)
	}
}

// SetStringMapValues writes string map values into a YAML mapping node.
func SetStringMapValues(mapNode *yaml.Node, fields map[string]string, opts SetValueOptions) {
	if mapNode == nil {
		return
	}
	keys := make([]string, 0, len(fields))
	for key := range fields {
		keys = append(keys, key)
	}
	if opts.SortKeys {
		sort.Strings(keys)
	}
	for _, key := range keys {
		SetValue(mapNode, key, fields[key], opts)
	}
}

// SetValue replaces the value under a YAML mapping key with a scalar, mapping,
// or sequence. A nil value deletes the key. SetMapValues is the API for
// merging a set of fields into an existing mapping. Unsupported value types and
// unrepresentable collection branches are written as quoted diagnostic strings.
func SetValue(mapNode *yaml.Node, key string, value any, opts SetValueOptions) {
	if value == nil {
		DeleteKey(mapNode, key)
		return
	}
	if text, ok := value.(string); ok && opts.DeleteEmptyStrings && strings.TrimSpace(text) == "" {
		DeleteKey(mapNode, key)
		return
	}

	// Normalize once before choosing the scalar-preserving or collection path.
	// This gives a supported Go value the same YAML kind/tag regardless of
	// whether it appears directly, inside a mapping, or inside a sequence.
	orderedValue := orderedValueForSet(value, opts)
	switch v := orderedValue.(type) {
	case string:
		SetScalarString(mapNode, key, v)
	case bool:
		SetScalarBool(mapNode, key, v)
	case int64:
		setScalarInt64(mapNode, key, v)
	case uint64:
		setScalarUint64(mapNode, key, v)
	case float64:
		SetScalarFloat(mapNode, key, v)
	case json.Number:
		setScalarJSONNumber(mapNode, key, v)
	default:
		setNodeValue(mapNode, key, orderedToYAMLNode(orderedValue), orderedValue)
	}
}

// DeleteKey removes all occurrences of 'key' under 'mapNode'.
// Surgical deletion removes the complete lines for the key’s occurrences.
// If exact deletion and a scoped rewrite are both unsafe, Marshal returns an
// error instead of globally re-encoding unrelated content.
func DeleteKey(mapNode *yaml.Node, key string) {
	if mapNode == nil {
		return
	}

	st, doc, isDocument, registered := findRegisteredNodeOwner(mapNode)
	var pathTokens []ptrToken
	if registered {
		if isDocument {
			return
		}
		st.mu.Lock()
		defer st.mu.Unlock()
		noteDirectASTMutationLocked(st)
		root := st.root()
		if root == nil || root != doc || len(root.Content) == 0 || mapNode.Kind != yaml.MappingNode {
			return
		}
		if exact, ok := addressableTokenPathToNode(root.Content[0], mapNode); ok {
			pathTokens = exact
		} else {
			return
		}
	} else {
		st = nil
		if mapNode.Kind != yaml.MappingNode {
			return
		}
	}
	if hasNonStringMappingKeyNamed(mapNode, key) {
		return
	}

	// Remove all pairs from the AST for the mapping node.
	found := false
	var retainedOld *yaml.Node
	nc := make([]*yaml.Node, 0, len(mapNode.Content))
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		v := mapNode.Content[i+1]
		if isStringMappingKey(k, key) {
			// drop the pair (k, v)
			_ = v
			found = true
			retainedOld = v
			continue
		}
		nc = append(nc, k, v)
	}
	mapNode.Content = nc

	if st == nil {
		return
	}
	if !found {
		return
	}
	fullPath := append(tokenPathSegments(pathTokens), key)
	recordNodeRemovalIntentLocked(st, fullPath, retainedOld)
	clearForcedScalarIntentAtOrBelow(st, fullPath)

	// Update ordered map and mark deletion for surgery.
	fullTokens := append(append([]ptrToken(nil), pathTokens...), ptrToken{key: key})
	if updated, err := orderedRemoveAtPathTokens(st.ordered, fullTokens); err == nil {
		st.ordered = updated
	}
	st.toDelete[makePathKey(tokenPathSegments(pathTokens), key)] = struct{}{}
	recordExpectedASTLocked(st)
}

// Ordered-map helpers shared by the setter helpers.
func ensureOrderedPath(ms gyaml.MapSlice, keys ...string) gyaml.MapSlice {
	if len(keys) == 0 {
		return ms
	}
	k := keys[0]
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, k) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = ensureOrderedPath(sub, keys[1:]...)
			ms[i].Value = sub
			return ms
		}
	}
	ms = append(ms, gyaml.MapItem{Key: k, Value: ensureOrderedPath(gyaml.MapSlice{}, keys[1:]...)})
	return ms
}

// Set the LAST occurrence if duplicates exist; else append.
func setIntAtPath(ms gyaml.MapSlice, path []string, key string, val int) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}

	head := path[0]
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setIntAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setIntAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

// string version mirrors int semantics (last occurrence wins; append if missing)
func setStringAtPath(ms gyaml.MapSlice, path []string, key, val string) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}
	head := path[0]
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setStringAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setStringAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

func setBoolAtPath(ms gyaml.MapSlice, path []string, key string, val bool) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}
	head := path[0]
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setBoolAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setBoolAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

func setFloatAtPath(ms gyaml.MapSlice, path []string, key string, val float64) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}
	head := path[0]
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setFloatAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setFloatAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

func setNullAtPath(ms gyaml.MapSlice, path []string, key string) gyaml.MapSlice {
	if len(path) == 0 {
		// store nil
		return setAnyAtPath(ms, path, key, nil)
	}
	head := path[0]
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setNullAtPath(sub, path[1:], key)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setNullAtPath(gyaml.MapSlice{}, path[1:], key)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

// delete a key at path (remove all occurrences)
func deleteKeyAtPath(ms gyaml.MapSlice, path []string, key string) (gyaml.MapSlice, bool) {
	if len(path) == 0 {
		out := make(gyaml.MapSlice, 0, len(ms))
		removed := false
		for _, it := range ms {
			if keyEquals(it.Key, key) {
				removed = true
				continue
			}
			out = append(out, it)
		}
		return out, removed
	}
	head := path[0]
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, head) {
			if sub, ok := ms[i].Value.(gyaml.MapSlice); ok {
				newSub, rem := deleteKeyAtPath(sub, path[1:], key)
				ms[i].Value = newSub
				return ms, rem
			}
			return ms, false
		}
	}
	return ms, false
}

// setAnyAtPath sets arbitrary value at a path/key (last segment is a key).
func setAnyAtPath(ms gyaml.MapSlice, path []string, key string, val interface{}) gyaml.MapSlice {
	if len(path) == 0 {
		for i := len(ms) - 1; i >= 0; i-- {
			if keyEquals(ms[i].Key, key) {
				ms[i].Value = val
				return ms
			}
		}
		ms = append(ms, gyaml.MapItem{Key: key, Value: val})
		return ms
	}
	head := path[0]
	for i := len(ms) - 1; i >= 0; i-- {
		if keyEquals(ms[i].Key, head) {
			sub, _ := ms[i].Value.(gyaml.MapSlice)
			sub = setAnyAtPath(sub, path[1:], key, val)
			ms[i].Value = sub
			return ms
		}
	}
	sub := setAnyAtPath(gyaml.MapSlice{}, path[1:], key, val)
	ms = append(ms, gyaml.MapItem{Key: head, Value: sub})
	return ms
}

func setNodeValue(mapNode *yaml.Node, key string, valueNode *yaml.Node, orderedValue any) {
	if mapNode == nil || valueNode == nil {
		return
	}

	// Classify registered handles before inspecting mutable node fields. This
	// mirrors the scalar setters: an attached node is validated while its
	// owning document is locked, and a stale/detached handle is ignored.
	st, docHN, isDocument, registered := findRegisteredNodeOwner(mapNode)
	var pathTokens []ptrToken
	if registered {
		if isDocument {
			return
		}
		st.mu.Lock()
		defer st.mu.Unlock()
		noteDirectASTMutationLocked(st)
		root := st.root()
		if root == nil || root != docHN || len(root.Content) == 0 || mapNode.Kind != yaml.MappingNode {
			return
		}
		var reachable bool
		pathTokens, reachable = addressableTokenPathToNode(root.Content[0], mapNode)
		if !reachable {
			return
		}
	} else {
		st = nil
		if mapNode.Kind != yaml.MappingNode {
			return
		}
	}
	if hasNonStringMappingKeyNamed(mapNode, key) {
		return
	}
	var oldNode *yaml.Node
	var retainedKeyNode *yaml.Node
	retainedPairIndex := -1
	for index := len(mapNode.Content) - 2; index >= 0; index -= 2 {
		if isStringMappingKey(mapNode.Content[index], key) {
			retainedKeyNode = mapNode.Content[index]
			oldNode = mapNode.Content[index+1]
			retainedPairIndex = index
			break
		}
	}
	// An alias stores a pointer to its anchor node, not merely the anchor name.
	// Replacing that pointer would leave every external alias aimed at a detached
	// node. Record the replacement intent before reusing the node below, so the
	// intent still remembers the original kind/tag.
	reuseAnchoredNode := oldNode != nil && oldNode.Anchor != ""

	var updatedOrdered gyaml.MapSlice
	if st != nil {
		fullTokens := append(append([]ptrToken(nil), pathTokens...), ptrToken{key: key})
		var err error
		updatedOrdered, err = orderedReplaceAtPathTokens(st.ordered, fullTokens, orderedValue)
		if err != nil {
			return
		}
		fullPath := tokenPathSegments(fullTokens)
		recordNodeReplacementIntentLocked(st, fullPath, oldNode, signatureOfYAMLNode(valueNode))
		markWholeCollectionReplacementIntentLocked(st, fullPath)
	}
	if oldNode != nil {
		if valueNode.HeadComment == "" {
			valueNode.HeadComment = oldNode.HeadComment
		}
		if valueNode.LineComment == "" {
			valueNode.LineComment = oldNode.LineComment
		}
		if valueNode.FootComment == "" {
			valueNode.FootComment = oldNode.FootComment
		}
		if valueNode.Line == 0 {
			valueNode.Line = oldNode.Line
		}
		if valueNode.Column == 0 {
			valueNode.Column = oldNode.Column
		}
		if oldNode.Kind == yaml.ScalarNode &&
			(valueNode.Kind == yaml.MappingNode || valueNode.Kind == yaml.SequenceNode) &&
			len(valueNode.Content) > 0 && oldNode.LineComment != "" {
			if retainedKeyNode != nil && retainedKeyNode.LineComment == "" {
				retainedKeyNode.LineComment = oldNode.LineComment
			}
			if valueNode.LineComment == oldNode.LineComment {
				valueNode.LineComment = ""
			}
		}
	}

	if reuseAnchoredNode {
		// Retain the presentation attached to the exact source node, while kind
		// and tag deliberately come from valueNode: SetValue replaces a custom-
		// tagged value with the ordinary tag of the requested Go collection.
		anchor := oldNode.Anchor
		line := oldNode.Line
		column := oldNode.Column

		*oldNode = *valueNode
		oldNode.Anchor = anchor
		oldNode.Line = line
		oldNode.Column = column
		valueNode = oldNode
	}

	nextContent := make([]*yaml.Node, 0, len(mapNode.Content)+2)
	replacementInserted := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		keyNode := mapNode.Content[i]
		if isStringMappingKey(keyNode, key) {
			// Replacing an existing key retains the last occurrence's mapping
			// position while earlier duplicates are removed. Besides matching the
			// public ordering contract, this keeps an anchored replacement before
			// any aliases that already refer to it.
			if i == retainedPairIndex {
				nextContent = append(nextContent, keyNode, valueNode)
				replacementInserted = true
			}
			continue
		}
		nextContent = append(nextContent, keyNode, mapNode.Content[i+1])
	}
	if !replacementInserted {
		nextContent = append(nextContent, &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}, valueNode)
	}
	mapNode.Content = nextContent

	if st == nil {
		return
	}

	fullTokens := append(append([]ptrToken(nil), pathTokens...), ptrToken{key: key})
	st.ordered = updatedOrdered
	clearDeletionMarkersAtOrBelow(st, tokenPathSegments(fullTokens))

	if valueNode.Kind == yaml.MappingNode {
		if path, ok := mappingOnlyTokenPath(fullTokens); ok {
			indexMappingHandles(st, valueNode, path)
		}
	}
	recordExpectedASTLocked(st)
}

// orderedReplaceAtPathTokens replaces the final mapping member while retaining
// its position and removing earlier duplicate occurrences. A missing final key
// is appended. Intermediate containers must already exist.
func orderedReplaceAtPathTokens(ms gyaml.MapSlice, path []ptrToken, value interface{}) (gyaml.MapSlice, error) {
	if len(path) == 0 {
		return ms, fmt.Errorf("orderedReplaceAtPath: empty path")
	}
	var recur func(interface{}, int) (interface{}, error)
	recur = func(current interface{}, depth int) (interface{}, error) {
		token := path[depth]
		switch container := current.(type) {
		case gyaml.MapSlice:
			last := -1
			for index := len(container) - 1; index >= 0; index-- {
				if keyEquals(container[index].Key, token.key) {
					last = index
					break
				}
			}
			if depth == len(path)-1 {
				if last < 0 {
					return append(container, gyaml.MapItem{Key: token.key, Value: value}), nil
				}
				replaced := make(gyaml.MapSlice, 0, len(container))
				for index, item := range container {
					if keyEquals(item.Key, token.key) {
						if index == last {
							item.Value = value
							replaced = append(replaced, item)
						}
						continue
					}
					replaced = append(replaced, item)
				}
				return replaced, nil
			}
			if last < 0 {
				return nil, fmt.Errorf("orderedReplaceAtPath: key %q not found", token.key)
			}
			next, err := recur(container[last].Value, depth+1)
			if err != nil {
				return nil, err
			}
			container[last].Value = next
			return container, nil
		case []interface{}:
			if !token.isIdx || token.append || token.index < 0 || token.index >= len(container) {
				return nil, fmt.Errorf("orderedReplaceAtPath: invalid sequence index at segment %d", depth)
			}
			if depth == len(path)-1 {
				container[token.index] = value
				return container, nil
			}
			next, err := recur(container[token.index], depth+1)
			if err != nil {
				return nil, err
			}
			container[token.index] = next
			return container, nil
		default:
			return nil, fmt.Errorf("orderedReplaceAtPath: unexpected type at segment %d (%T)", depth, current)
		}
	}

	updated, err := recur(ms, 0)
	if err != nil {
		return ms, err
	}
	result, ok := updated.(gyaml.MapSlice)
	if !ok {
		return ms, fmt.Errorf("orderedReplaceAtPath: root changed to %T", updated)
	}
	return result, nil
}

const (
	// Keep caller-controlled collection graphs comfortably below the recursion
	// depths used by the encoders and the ordered-shadow helpers. SetValue has no
	// error return, so an unrepresentable branch is preserved as a diagnostic
	// string instead of panicking or recursing without bound.
	setValueMaxNestingDepth = 256
	setValueNodeBudget      = 100_000

	setValueCycleMarker = "<yamledit: cyclic value>"
	setValueDepthMarker = "<yamledit: value nesting limit exceeded>"
	setValueSizeMarker  = "<yamledit: value size limit exceeded>"
	setValueTypeMarker  = "<yamledit: unsupported value type>"
)

type setValueContainerIdentity struct {
	kind reflect.Kind
	ptr  uintptr
	len  int
	cap  int
}

type setValueNormalizer struct {
	visiting  map[setValueContainerIdentity]struct{}
	remaining int
}

func orderedValueForSet(value any, opts SetValueOptions) any {
	normalizer := setValueNormalizer{
		visiting:  make(map[setValueContainerIdentity]struct{}),
		remaining: setValueNodeBudget,
	}
	return normalizer.normalize(value, opts, 0)
}

func (n *setValueNormalizer) normalize(value any, opts SetValueOptions, depth int) any {
	if n.remaining <= 0 {
		return setValueSizeMarker
	}
	n.remaining--

	switch v := value.(type) {
	case map[string]any:
		if depth >= setValueMaxNestingDepth {
			return setValueDepthMarker
		}
		identity := setValueContainerID(v)
		if _, cyclic := n.visiting[identity]; cyclic {
			return setValueCycleMarker
		}
		n.visiting[identity] = struct{}{}
		defer delete(n.visiting, identity)

		// Refuse an over-budget container before allocating and walking its keys.
		// The remaining budget is also shared by its descendants.
		if len(v) > n.remaining {
			n.remaining = 0
			return setValueSizeMarker
		}
		keys := make([]string, 0, len(v))
		for key := range v {
			keys = append(keys, key)
		}
		if opts.SortKeys {
			sort.Strings(keys)
		}
		items := make(gyaml.MapSlice, 0, len(keys))
		for _, key := range keys {
			if v[key] == nil {
				// A nil passed for a mapping field has the same deletion/omission
				// meaning as SetValue(mapping, key, nil, opts).
				continue
			}
			if text, ok := v[key].(string); ok && opts.DeleteEmptyStrings && strings.TrimSpace(text) == "" {
				continue
			}
			items = append(items, gyaml.MapItem{Key: key, Value: n.normalize(v[key], opts, depth+1)})
		}
		return items
	case []string:
		if depth >= setValueMaxNestingDepth {
			return setValueDepthMarker
		}
		if len(v) > n.remaining {
			n.remaining = 0
			return setValueSizeMarker
		}
		n.remaining -= len(v)
		out := make([]any, 0, len(v))
		for _, item := range v {
			out = append(out, item)
		}
		return out
	case []any:
		if depth >= setValueMaxNestingDepth {
			return setValueDepthMarker
		}
		identity := setValueContainerID(v)
		if _, cyclic := n.visiting[identity]; cyclic {
			return setValueCycleMarker
		}
		n.visiting[identity] = struct{}{}
		defer delete(n.visiting, identity)

		if len(v) > n.remaining {
			n.remaining = 0
			return setValueSizeMarker
		}
		out := make([]any, 0, len(v))
		for _, item := range v {
			out = append(out, n.normalize(item, opts, depth+1))
		}
		return out
	case int:
		return int64(v)
	case int8:
		return int64(v)
	case int16:
		return int64(v)
	case int32:
		return int64(v)
	case int64:
		return v
	case uint:
		return uint64(v)
	case uint8:
		return uint64(v)
	case uint16:
		return uint64(v)
	case uint32:
		return uint64(v)
	case uint64:
		return v
	case uintptr:
		return uint64(v)
	case float32:
		return float64(v)
	case float64, bool, string, nil:
		return v
	case json.Number:
		if !isValidJSONNumber(v) {
			// SetValue cannot return a validation error, so preserve the caller's
			// text as a YAML string, never as trusted syntax that could escape its
			// containing value.
			return string(v)
		}
		return v
	default:
		return setValueTypeMarker
	}
}

func setValueContainerID(value any) setValueContainerIdentity {
	rv := reflect.ValueOf(value)
	identity := setValueContainerIdentity{kind: rv.Kind(), ptr: rv.Pointer()}
	if rv.Kind() == reflect.Slice {
		// Slices sharing a backing array are not necessarily the same logical
		// container. Include the complete header shape so only a recursive visit
		// to the same view is classified as a cycle.
		identity.len = rv.Len()
		identity.cap = rv.Cap()
	}
	return identity
}
