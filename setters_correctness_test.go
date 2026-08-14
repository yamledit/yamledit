package yamledit

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func mappingValueForStringKey(t *testing.T, mapping *yaml.Node, key string) *yaml.Node {
	t.Helper()
	require.NotNil(t, mapping)
	require.Equal(t, yaml.MappingNode, mapping.Kind)
	for i := len(mapping.Content) - 2; i >= 0; i -= 2 {
		if mapping.Content[i] != nil && mapping.Content[i].Kind == yaml.ScalarNode && mapping.Content[i].Value == key {
			return mapping.Content[i+1]
		}
	}
	t.Fatalf("mapping key %q not found", key)
	return nil
}

func TestEnsurePathClearsDeletionMarkerWhenRecreatingPath(t *testing.T) {
	t.Run("root mapping", func(t *testing.T) {
		doc, err := Parse([]byte("obj:\n  old: 1\nkeep: yes\n"))
		require.NoError(t, err)

		DeleteKey(doc.Content[0], "obj")
		recreated := EnsurePath(doc, "obj")
		require.NotNil(t, recreated)
		SetScalarInt(recreated, "new", 2)

		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]interface{}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, map[string]interface{}{"new": 2}, got["obj"])
		require.Equal(t, "yes", got["keep"])
	})

	t.Run("mapping inside sequence", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - obj:\n      old: 1\n    keep: yes\n"))
		require.NoError(t, err)
		item := doc.Content[0].Content[1].Content[0]

		DeleteKey(item, "obj")
		recreated := EnsurePath(item, "obj")
		require.NotNil(t, recreated)
		SetScalarInt(recreated, "new", 2)

		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []map[string]interface{} `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Len(t, got.Items, 1)
		require.Equal(t, map[string]interface{}{"new": 2}, got.Items[0]["obj"])
		require.Equal(t, "yes", got.Items[0]["keep"])
	})
}

func TestEnsurePathDoesNotClearUnrelatedDeletionMarker(t *testing.T) {
	doc, err := Parse([]byte("root:\n  remove: gone\n  keep: yes\n"))
	require.NoError(t, err)
	root := EnsurePath(doc, "root")
	require.NotNil(t, root)

	DeleteKey(root, "remove")
	created := EnsurePath(root, "created")
	require.NotNil(t, created)
	SetScalarInt(created, "value", 1)

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]map[string]interface{}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.NotContains(t, got["root"], "remove")
	require.Equal(t, map[string]interface{}{"value": 1}, got["root"]["created"])
}

func TestSetValueQuotesInvalidJSONNumbersRecursively(t *testing.T) {
	malicious := json.Number("1\ninjected: yes")
	for _, input := range [][]byte{nil, []byte("keep: yes\n")} {
		doc, err := Parse(input)
		require.NoError(t, err)

		SetValue(doc.Content[0], "direct", malicious, SetValueOptions{})
		SetValue(doc.Content[0], "values", []any{
			malicious,
			map[string]any{"comment": json.Number("1 # forged")},
		}, SetValueOptions{SortKeys: true})

		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]interface{}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.NotContains(t, got, "injected", "output:\n%s", out)
		require.Equal(t, string(malicious), got["direct"])
		values, ok := got["values"].([]interface{})
		require.True(t, ok, "output:\n%s", out)
		require.Equal(t, string(malicious), values[0])
		require.Equal(t, "1 # forged", values[1].(map[string]interface{})["comment"])
	}
}

func TestSetValueKeepsValidNestedJSONNumberNumeric(t *testing.T) {
	doc, err := Parse([]byte("keep: yes\n"))
	require.NoError(t, err)
	SetValue(doc.Content[0], "values", []any{json.Number("9007199254740993.0")}, SetValueOptions{})

	out, err := Marshal(doc)
	require.NoError(t, err)
	var round yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
	values := round.Content[0].Content[3]
	require.Equal(t, yaml.SequenceNode, values.Kind, "output:\n%s", out)
	require.Len(t, values.Content, 1)
	require.Equal(t, "!!float", values.Content[0].Tag, "output:\n%s", out)
	require.Equal(t, "9007199254740993.0", values.Content[0].Value)
}

func TestSetValueTreatsValidJSONNumberConsistentlyAtEveryDepth(t *testing.T) {
	number := json.Number("9007199254740993.0")
	doc, err := Parse([]byte("keep: yes\n"))
	require.NoError(t, err)
	root := doc.Content[0]

	SetValue(root, "direct", number, SetValueOptions{})
	SetMapValues(root, map[string]any{
		"nested": map[string]any{"number": number},
	}, SetValueOptions{SortKeys: true})
	SetValue(root, "sequence", []any{number}, SetValueOptions{})

	out, err := Marshal(doc)
	require.NoError(t, err)
	var round yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
	mapping := round.Content[0]
	assertNumber := func(node *yaml.Node) {
		require.Equal(t, yaml.ScalarNode, node.Kind, "output:\n%s", out)
		require.Equal(t, "!!float", node.Tag, "output:\n%s", out)
		require.Equal(t, number.String(), node.Value, "output:\n%s", out)
	}
	assertNumber(mappingValueForStringKey(t, mapping, "direct"))
	nested := mappingValueForStringKey(t, mapping, "nested")
	assertNumber(mappingValueForStringKey(t, nested, "number"))
	sequence := mappingValueForStringKey(t, mapping, "sequence")
	require.Equal(t, yaml.SequenceNode, sequence.Kind, "output:\n%s", out)
	require.Len(t, sequence.Content, 1)
	assertNumber(sequence.Content[0])
}

func TestComplexMutationHistoryFallsBackToCompleteTypedRewrite(t *testing.T) {
	input := []byte("# header\ntarget: 'old' # target\nitems:\n  - name: first\n    value: !!str old # item\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	root := doc.Content[0]

	// Exercise repeated scalar/collection/tag transitions before a second edit
	// elsewhere. The first surgical candidate cannot represent every transition;
	// Marshal must reject that candidate and complete the scoped structural edit.
	SetScalarInt(root, "target", 4)
	SetValue(root, "target", map[string]any{"a": json.Number("1.0"), "b": true}, SetValueOptions{SortKeys: true})
	SetScalarNull(root, "target")
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[
		{"op":"remove","path":"/target"},
		{"op":"add","path":"/target","value":"restored"},
		{"op":"replace","path":"/items/0/value","value":1e999}
	]`)))
	SetScalarString(root, "target", "multi\nline")

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "!!str", scalarForKey(t, out, "target").Tag, "output:\n%s", out)
	require.Equal(t, "multi\nline", scalarForKey(t, out, "target").Value, "output:\n%s", out)

	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
	items := mappingValueForStringKey(t, reparsed.Content[0], "items")
	require.Equal(t, yaml.SequenceNode, items.Kind, "output:\n%s", out)
	require.Len(t, items.Content, 1, "output:\n%s", out)
	itemValue := mappingValueForStringKey(t, items.Content[0], "value")
	require.Equal(t, "!!float", itemValue.Tag, "output:\n%s", out)
	require.Equal(t, "1e999", itemValue.Value, "output:\n%s", out)
	require.Contains(t, string(out), "# target")
	require.Contains(t, string(out), "# item")
}
