package yamledit

import (
	"fmt"
	"math"
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
// It now accepts either a root DocumentNode or a MappingNode as the starting point.
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

		if found == nil {
			key := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: k}
			val := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
			cur.Content = append(cur.Content, key, val)
			keyNode = key
			found = val
		}
		if found.Kind != yaml.MappingNode {
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
		}
		cur = found
		curTokens = append(curTokens, ptrToken{key: k})

		// Keep handle → path mapping up to date for new/converted nodes
		if st != nil {
			if keyPath, ok := mappingOnlyTokenPath(curTokens); ok {
				st.subPathByHN[weak.Make(cur)] = keyPath
			}
		}
	}

	// Keep ordered (logical) view in sync
	if st != nil {
		if updated, err := orderedEnsureMapPath(st.ordered, curTokens); err == nil {
			st.ordered = updated
		} else {
			st.structuralDirty = true
		}
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
			setScalarNode(mapNode.Content[i+1], tag, val)
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
	updateOrdered func(ms gyaml.MapSlice, path []string, key string) gyaml.MapSlice,
) {
	if mapNode == nil {
		return
	}

	st, docHN, isDocument, registered := findRegisteredNodeOwner(mapNode)
	if registered {
		if isDocument {
			return
		}
		st.mu.Lock()
		defer st.mu.Unlock()
		root := st.root()
		if root == nil || root != docHN || len(root.Content) == 0 {
			return
		}
		if _, reachable := addressableTokenPathToNode(root.Content[0], mapNode); !reachable || mapNode.Kind != yaml.MappingNode {
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

	existed := false
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		if isStringMappingKey(mapNode.Content[i], key) {
			existed = true
			break
		}
	}

	// Always update the yaml.v3 AST first.
	upsertScalarKey(mapNode, key, tag, val)

	if st == nil {
		return
	}

	// If this mapping node is already indexed as a mapping (i.e. reachable by keys),
	// keep existing behavior and update the ordered MapSlice via the mapping path.
	mapRef := weak.Make(mapNode)
	if _, ok := st.subPathByHN[mapRef]; !ok && docHN != nil && len(docHN.Content) > 0 {
		indexMappingHandles(st, docHN.Content[0], nil)
	}
	if path, ok := st.subPathByHN[mapRef]; ok {
		st.ordered = updateOrdered(st.ordered, path, key)
		clearDeletionMarkersAtOrBelow(st, append(append([]string(nil), path...), key))
		return
	}

	// Mapping nodes inside sequences need an index-aware path. Resolve the
	// pointer directly from the locked AST so newly inserted fields (which have
	// no source Line/Column) can still update the ordered shadow correctly.
	if root := st.root(); root != nil && len(root.Content) > 0 {
		if base, ok := addressableTokenPathToNode(root.Content[0], mapNode); ok {
			full := append(append([]ptrToken(nil), base...), ptrToken{key: key})
			logical := scalarLogicalValue(tag, val)
			if updated, err := orderedUpsertAtPathTokens(st.ordered, full, logical); err == nil {
				st.ordered = updated
				clearDeletionMarkersAtOrBelow(st, append(tokenPathSegments(base), key))
				if !existed {
					st.structuralDirty = true
				}
				return
			}
		}
	}

	// Otherwise, this mapping node is most likely an item inside a sequence.
	// In that case, we don't have a mapping-based path; instead, we locate the
	// scalar occurrence by its byte offset and update the ordered view using a
	// ptrToken path derived from valueOccByPathKey.
	if updateScalarInSequenceOrdered(st, mapNode, key, tag, val) {
		// sequence items are not tracked in toDelete, so nothing to clear there
		return
	}

	// If we couldn't reconcile the ordered view for this mapping, mark the
	// document as structurally dirty so surgery is avoided. (We still leave
	// the AST updated; Marshal may fall back to structural rewrite.)
	st.structuralDirty = true
}

func scalarLogicalValue(tag, val string) interface{} {
	switch tag {
	case "!!int":
		if i, err := strconv.Atoi(val); err == nil {
			return i
		}
		if i, err := strconv.ParseInt(val, 10, 64); err == nil {
			return i
		}
	case "!!bool":
		return strings.EqualFold(val, "true")
	case "!!float":
		switch strings.ToLower(val) {
		case ".nan":
			return math.NaN()
		case ".inf", "+.inf":
			return math.Inf(1)
		case "-.inf":
			return math.Inf(-1)
		}
		if f, err := strconv.ParseFloat(val, 64); err == nil {
			return f
		}
	case "!!null":
		return nil
	}
	return val
}

// updateScalarInSequenceOrdered updates st.ordered for a scalar that lives inside
// a mapping which itself is an item of a sequence. It discovers the logical
// ptrToken path by matching the scalar node's byte position against
// valueOccByPathKey entries and then calls orderedSetAtPathTokens.
func updateScalarInSequenceOrdered(st *docState, mapNode *yaml.Node, key, tag, val string) bool {
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

	logical := scalarLogicalValue(tag, val)

	newOrdered, err := orderedSetAtPathTokens(st.ordered, toks, logical)
	if err != nil {
		return false
	}
	st.ordered = newOrdered
	return true
}

// SetScalarInt sets an integer value under the mapping node.
func SetScalarInt(mapNode *yaml.Node, key string, value int) {
	valStr := fmt.Sprintf("%d", value)
	setScalarValue(mapNode, key, "!!int", valStr, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setIntAtPath(ms, path, k, value)
	})
}

func setScalarInt64(mapNode *yaml.Node, key string, value int64) {
	valStr := strconv.FormatInt(value, 10)
	setScalarValue(mapNode, key, "!!int", valStr, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setAnyAtPath(ms, path, k, value)
	})
}

func float64FitsInt(value float64) bool {
	if math.IsNaN(value) || math.IsInf(value, 0) || math.Trunc(value) != value {
		return false
	}
	if strconv.IntSize == 32 {
		return value >= -(1<<31) && value <= 1<<31-1
	}
	limit := math.Ldexp(1, 63)
	return value >= -limit && value < limit
}

// SetScalarString sets a string value under the mapping node.
func SetScalarString(mapNode *yaml.Node, key, value string) {
	setScalarValue(mapNode, key, "!!str", value, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
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

	setScalarValue(mapNode, key, "!!bool", valStr, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setBoolAtPath(ms, path, k, value)
	})
}

// SetScalarFloat sets a float value under the mapping node.
func SetScalarFloat(mapNode *yaml.Node, key string, value float64) {
	valStr := formatYAMLFloat(value)
	setScalarValue(mapNode, key, "!!float", valStr, func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
		return setFloatAtPath(ms, path, k, value)
	})
}

// SetScalarNull sets a null value (!!null) under the mapping node.
func SetScalarNull(mapNode *yaml.Node, key string) {
	setScalarValue(mapNode, key, "!!null", "null", func(ms gyaml.MapSlice, path []string, k string) gyaml.MapSlice {
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

// SetValue writes a scalar, mapping, or sequence value under a YAML mapping key.
func SetValue(mapNode *yaml.Node, key string, value any, opts SetValueOptions) {
	switch v := value.(type) {
	case nil:
		DeleteKey(mapNode, key)
	case string:
		if opts.DeleteEmptyStrings && strings.TrimSpace(v) == "" {
			DeleteKey(mapNode, key)
		} else {
			SetScalarString(mapNode, key, v)
		}
	case bool:
		SetScalarBool(mapNode, key, v)
	case int:
		SetScalarInt(mapNode, key, v)
	case int64:
		if strconv.IntSize == 64 || (v >= -(1<<31) && v <= 1<<31-1) {
			SetScalarInt(mapNode, key, int(v))
		} else {
			setScalarInt64(mapNode, key, v)
		}
	case float32:
		SetScalarFloat(mapNode, key, float64(v))
	case float64:
		if float64FitsInt(v) {
			SetScalarInt(mapNode, key, int(v))
		} else {
			SetScalarFloat(mapNode, key, v)
		}
	case []string:
		values := make([]any, 0, len(v))
		for _, item := range v {
			values = append(values, item)
		}
		setSequenceValue(mapNode, key, values, opts)
	case []any:
		setSequenceValue(mapNode, key, v, opts)
	case map[string]any:
		child := EnsurePath(mapNode, key)
		SetMapValues(child, v, opts)
	default:
		SetScalarString(mapNode, key, fmt.Sprintf("%v", v))
	}
}

// DeleteKey removes all occurrences of 'key' under 'mapNode'.
// Surgical deletion removes the complete lines for the key’s occurrences.
// If surgery is unsafe/unavailable, Marshal() falls back to a structured re-encode.
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
	nc := make([]*yaml.Node, 0, len(mapNode.Content))
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		k := mapNode.Content[i]
		v := mapNode.Content[i+1]
		if isStringMappingKey(k, key) {
			// drop the pair (k, v)
			_ = v
			found = true
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

	if len(mapNode.Content) == 0 {
		st.structuralDirty = true
	}

	// Update ordered map and mark deletion for surgery.
	fullTokens := append(append([]ptrToken(nil), pathTokens...), ptrToken{key: key})
	if updated, err := orderedRemoveAtPathTokens(st.ordered, fullTokens); err == nil {
		st.ordered = updated
	} else {
		st.structuralDirty = true
	}
	st.toDelete[makePathKey(tokenPathSegments(pathTokens), key)] = struct{}{}
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

func setSequenceValue(mapNode *yaml.Node, key string, values []any, opts SetValueOptions) {
	if len(values) == 0 {
		DeleteKey(mapNode, key)
		return
	}
	orderedValue := orderedValueForSet(values, opts)
	setNodeValue(mapNode, key, orderedToYAMLNode(orderedValue), orderedValue)
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

	var updatedOrdered gyaml.MapSlice
	if st != nil {
		fullTokens := append(append([]ptrToken(nil), pathTokens...), ptrToken{key: key})
		base := st.ordered
		// setNodeValue removes every duplicate string-key occurrence from the
		// AST, so remove logical duplicates before appending the replacement.
		if withoutOld, err := orderedRemoveAtPathTokens(base, fullTokens); err == nil {
			base = withoutOld
		}
		var err error
		updatedOrdered, err = orderedUpsertAtPathTokens(base, fullTokens, orderedValue)
		if err != nil {
			return
		}
	}

	nextContent := make([]*yaml.Node, 0, len(mapNode.Content)+2)
	for i := 0; i+1 < len(mapNode.Content); i += 2 {
		keyNode := mapNode.Content[i]
		if isStringMappingKey(keyNode, key) {
			continue
		}
		nextContent = append(nextContent, keyNode, mapNode.Content[i+1])
	}
	nextContent = append(nextContent, &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: key}, valueNode)
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
	// Complex values have no source offsets, so force the safe structural
	// renderer rather than attempting scalar byte surgery.
	st.structuralDirty = true
}

func orderedValueForSet(value any, opts SetValueOptions) any {
	switch v := value.(type) {
	case map[string]any:
		keys := make([]string, 0, len(v))
		for key := range v {
			keys = append(keys, key)
		}
		if opts.SortKeys {
			sort.Strings(keys)
		}
		items := make(gyaml.MapSlice, 0, len(keys))
		for _, key := range keys {
			items = append(items, gyaml.MapItem{Key: key, Value: orderedValueForSet(v[key], opts)})
		}
		return items
	case []string:
		out := make([]any, 0, len(v))
		for _, item := range v {
			out = append(out, item)
		}
		return out
	case []any:
		out := make([]any, 0, len(v))
		for _, item := range v {
			out = append(out, orderedValueForSet(item, opts))
		}
		return out
	default:
		return v
	}
}
