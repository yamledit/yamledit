package yamledit

import (
	"bytes"
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestNewKeyTypeChangeDoesNotPlanDuplicateInsertion(t *testing.T) {
	doc, err := Parse([]byte("target: {old: 1,\n nested: [a, b]}\nkeep: yes\n"))
	require.NoError(t, err)
	root := doc.Content[0]

	SetMapValues(root, map[string]any{
		"extra":   int16(49),
		"history": []string{"kept", ""},
	}, SetValueOptions{SortKeys: true})
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/target","value":["a",3]}]`)))
	SetScalarString(root, "extra", "a: b")

	out, err := Marshal(doc)
	require.NoError(t, err)

	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
	reparsedRoot := reparsed.Content[0]
	extraOccurrences := 0
	var extra *yaml.Node
	for index := 0; index+1 < len(reparsedRoot.Content); index += 2 {
		if isStringMappingKey(reparsedRoot.Content[index], "extra") {
			extraOccurrences++
			extra = reparsedRoot.Content[index+1]
		}
	}
	require.Equal(t, 1, extraOccurrences, "output:\n%s", out)
	require.NotNil(t, extra)
	require.Equal(t, yaml.ScalarNode, extra.Kind)
	require.Equal(t, "!!str", extra.Tag)
	require.Equal(t, "a: b", extra.Value)

	roundTrip, err := Parse(out)
	require.NoError(t, err)
	second, err := Marshal(roundTrip)
	require.NoError(t, err)
	require.True(t, bytes.Equal(out, second), "first:\n%s\nsecond:\n%s", out, second)
}

func TestRemovedThenRecreatedKeyUsesFinalMappingPosition(t *testing.T) {
	for _, tc := range []struct {
		name string
		edit func(*yaml.Node, *yaml.Node)
	}{
		{
			name: "setters",
			edit: func(doc, root *yaml.Node) {
				DeleteKey(root, "target")
				SetScalarString(root, "target", "old")
			},
		},
		{
			name: "JSON Patch",
			edit: func(doc, _ *yaml.Node) {
				require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[
					{"op":"remove","path":"/target"},
					{"op":"add","path":"/target","value":"old"}
				]`)))
			},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			doc, err := Parse([]byte("target: old # removed with key\nkeep: yes\n"))
			require.NoError(t, err)
			tc.edit(doc, doc.Content[0])

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, "keep: yes\ntarget: old # removed with key\n", string(out))

			reparsed, err := Parse(out)
			require.NoError(t, err)
			require.Equal(t, "keep", reparsed.Content[0].Content[0].Value)
			require.Equal(t, "target", reparsed.Content[0].Content[2].Value)
		})
	}
}

func TestRemovedThenRecreatedSequenceMappingKeySurvivesTransientIndexShift(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - target: old\n    keep: yes\n"))
	require.NoError(t, err)
	items := mappingValueForStringKey(t, doc.Content[0], "items")
	require.Equal(t, yaml.SequenceNode, items.Kind)
	require.Len(t, items.Content, 1)
	item := items.Content[0]

	DeleteKey(item, "target")
	SetScalarString(item, "target", "old")
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[
		{"op":"add","path":"/items/0","value":{"temporary":true}},
		{"op":"remove","path":"/items/0"}
	]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "items:\n  - keep: yes\n    target: old\n", string(out))
}

func TestJSONPatchRecreatedMappingKeyRestoresCommentsInLiveAST(t *testing.T) {
	doc, err := Parse([]byte("target: old # source comment\nkeep: yes\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[
		{"op":"remove","path":"/target"},
		{"op":"add","path":"/target","value":"old"}
	]`)))

	root := doc.Content[0]
	require.Equal(t, "keep", root.Content[0].Value)
	require.Equal(t, "target", root.Content[2].Value)
	require.Equal(t, "# source comment", root.Content[3].LineComment)

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "keep: yes\ntarget: old # source comment\n", string(out))

	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
	require.True(t, yamlNodeGraphEqual(doc, &reparsed), "live AST and serialized graph diverged\noutput:\n%s", out)
}
