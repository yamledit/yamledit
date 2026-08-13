package yamledit

import (
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func parsedRootValue(t *testing.T, output []byte, key string) *yaml.Node {
	t.Helper()
	var document yaml.Node
	require.NoError(t, yaml.Unmarshal(output, &document), "output:\n%s", output)
	require.Equal(t, yaml.DocumentNode, document.Kind)
	require.Len(t, document.Content, 1)
	return mappingValueForStringKey(t, document.Content[0], key)
}

func TestScalarTagIntentUsesRetainedDuplicateOccurrence(t *testing.T) {
	doc, err := Parse([]byte("x: !!str a\nx: !Widget a\n"))
	require.NoError(t, err)

	SetScalarString(doc.Content[0], "x", "a")
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "x: a\n", string(out))
	require.Equal(t, "!!str", parsedRootValue(t, out, "x").Tag)
}

func TestScalarTagIntentSurvivesDeleteAndRecreate(t *testing.T) {
	mutations := []struct {
		name   string
		mutate func(*yaml.Node) error
	}{
		{
			name: "setters",
			mutate: func(doc *yaml.Node) error {
				DeleteKey(doc.Content[0], "x")
				SetScalarString(doc.Content[0], "x", "a")
				return nil
			},
		},
		{
			name: "JSON Patch",
			mutate: func(doc *yaml.Node) error {
				return ApplyJSONPatchBytes(doc, []byte(`[
					{"op":"remove","path":"/x"},
					{"op":"add","path":"/x","value":"a"}
				]`))
			},
		},
	}

	for _, mutation := range mutations {
		t.Run(mutation.name, func(t *testing.T) {
			doc, err := Parse([]byte("x: !Widget a\nkeep: 1\n"))
			require.NoError(t, err)
			require.NoError(t, mutation.mutate(doc))

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, "!!str", parsedRootValue(t, out, "x").Tag, "output:\n%s", out)
			require.NotContains(t, string(out), "!Widget")
			require.Contains(t, string(out), "keep: 1")
		})
	}
}

func TestScalarTagIntentSurvivesIntermediateCollection(t *testing.T) {
	doc, err := Parse([]byte("x: !Widget a\nkeep: 1\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[
		{"op":"replace","path":"/x","value":{"nested":1}},
		{"op":"replace","path":"/x","value":"a"}
	]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "!!str", parsedRootValue(t, out, "x").Tag, "output:\n%s", out)
	require.NotContains(t, string(out), "!Widget")
}

func TestCollectionReplacementRemovesOriginalCustomTag(t *testing.T) {
	tests := []struct {
		name   string
		input  string
		patch  string
		key    string
		kind   yaml.Kind
		tag    string
		setter bool
	}{
		{name: "mapping same value", input: "x: !Widget {a: 1}\nkeep: 2\n", patch: `[{"op":"replace","path":"/x","value":{"a":1}}]`, key: "x", kind: yaml.MappingNode, tag: "!!map"},
		{name: "mapping changed value", input: "x: !Widget {a: 1}\nkeep: 2\n", patch: `[{"op":"replace","path":"/x","value":{"a":3}}]`, key: "x", kind: yaml.MappingNode, tag: "!!map"},
		{name: "sequence same value", input: "items: !Widget [1]\nkeep: 2\n", patch: `[{"op":"replace","path":"/items","value":[1]}]`, key: "items", kind: yaml.SequenceNode, tag: "!!seq"},
		{name: "sequence changed value", input: "items: !Widget [1]\nkeep: 2\n", patch: `[{"op":"replace","path":"/items","value":[3]}]`, key: "items", kind: yaml.SequenceNode, tag: "!!seq"},
		{name: "sequence setter", input: "items: !Widget [1]\nkeep: 2\n", key: "items", kind: yaml.SequenceNode, tag: "!!seq", setter: true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			if tt.setter {
				SetValue(doc.Content[0], "items", []any{1}, SetValueOptions{})
			} else {
				require.NoError(t, ApplyJSONPatchBytes(doc, []byte(tt.patch)))
			}

			out, err := Marshal(doc)
			require.NoError(t, err)
			value := parsedRootValue(t, out, tt.key)
			require.Equal(t, tt.kind, value.Kind, "output:\n%s", out)
			require.Equal(t, tt.tag, value.Tag, "output:\n%s", out)
			require.NotContains(t, string(out), "!Widget")
			require.Contains(t, string(out), "keep: 2")
		})
	}
}

func TestEditingInsideCustomCollectionPreservesItsTag(t *testing.T) {
	mutations := []struct {
		name   string
		mutate func(*yaml.Node) error
	}{
		{
			name: "setter",
			mutate: func(doc *yaml.Node) error {
				object := EnsurePath(doc, "object")
				require.NotNil(t, object)
				SetScalarInt(object, "value", 2)
				return nil
			},
		},
		{
			name: "JSON Patch",
			mutate: func(doc *yaml.Node) error {
				return ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/object/value","value":2}]`))
			},
		},
	}

	for _, mutation := range mutations {
		t.Run(mutation.name, func(t *testing.T) {
			doc, err := Parse([]byte("object: !Widget\n  value: 1\nkeep: 3\n"))
			require.NoError(t, err)
			require.NoError(t, mutation.mutate(doc))

			out, err := Marshal(doc)
			require.NoError(t, err)
			object := parsedRootValue(t, out, "object")
			require.Equal(t, "!Widget", object.Tag, "output:\n%s", out)
			require.Equal(t, 2, func() any {
				var decoded map[string]any
				require.NoError(t, object.Decode(&decoded))
				return decoded["value"]
			}())
			require.Contains(t, string(out), "keep: 3")
		})
	}
}

func TestSequenceItemTagIntentSurvivesRemoveAndReinsert(t *testing.T) {
	tests := []struct {
		name  string
		input string
		value string
		kind  yaml.Kind
		tag   string
	}{
		{name: "mapping", input: "items:\n  - !Widget {a: 1}\n  - keep\n", value: `{"a":1}`, kind: yaml.MappingNode, tag: "!!map"},
		{name: "sequence", input: "items:\n  - !Widget [1]\n  - keep\n", value: `[1]`, kind: yaml.SequenceNode, tag: "!!seq"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			patch := `[{"op":"remove","path":"/items/0"},{"op":"add","path":"/items/0","value":` + tt.value + `}]`
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(patch)))

			out, err := Marshal(doc)
			require.NoError(t, err)
			items := parsedRootValue(t, out, "items")
			require.Len(t, items.Content, 2, "output:\n%s", out)
			require.Equal(t, tt.kind, items.Content[0].Kind, "output:\n%s", out)
			require.Equal(t, tt.tag, items.Content[0].Tag, "output:\n%s", out)
			require.NotContains(t, string(out), "!Widget")
		})
	}
}

func TestSequenceTagIntentRebasesWithEarlierInsertion(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - first\n  - !Widget same\nkeep: 1\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[
		{"op":"replace","path":"/items/1","value":"same"},
		{"op":"add","path":"/items/-","value":"last"}
	]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	items := parsedRootValue(t, out, "items")
	require.Len(t, items.Content, 3, "output:\n%s", out)
	require.Equal(t, "!!str", items.Content[1].Tag, "output:\n%s", out)
	require.NotContains(t, string(out), "!Widget")
}

func TestSequenceTagIntentSurvivesInsertThenRemoveAtSameIndex(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - !Widget same\n  - same\n  - {kind: mapping}\nkeep: 1\n"))
	require.NoError(t, err)

	// First remove the source-only tag from item 0. Inserting another item at
	// index 0 shifts that intent to index 1; removing the inserted item must
	// shift it back rather than letting the removed item's tombstone win a path
	// collision.
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/items/0","value":"same"}]`)))
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/0","value":"same"}]`)))
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0"}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	items := parsedRootValue(t, out, "items")
	require.Len(t, items.Content, 3, "output:\n%s", out)
	require.Equal(t, "!!str", items.Content[0].Tag, "output:\n%s", out)
	require.NotContains(t, string(out), "!Widget")
	require.Contains(t, string(out), "keep: 1")
}

func TestSequenceCollectionTagIntentSurvivesInsertThenRemoveAtSameIndex(t *testing.T) {
	tests := []struct {
		name        string
		input       string
		replacement string
		inserted    string
		wantKind    yaml.Kind
	}{
		{
			name:        "mapping",
			input:       "items:\n  - !Widget {a: 1}\n  - keep\n",
			replacement: `{"a":1}`,
			inserted:    `{"temporary":true}`,
			wantKind:    yaml.MappingNode,
		},
		{
			name:        "sequence",
			input:       "items:\n  - !Widget [1]\n  - keep\n",
			replacement: `[1]`,
			inserted:    `["temporary"]`,
			wantKind:    yaml.SequenceNode,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/items/0","value":`+tt.replacement+`}]`)))
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/0","value":`+tt.inserted+`}]`)))
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0"}]`)))

			out, err := Marshal(doc)
			require.NoError(t, err)
			items := parsedRootValue(t, out, "items")
			require.Len(t, items.Content, 2, "output:\n%s", out)
			require.Equal(t, tt.wantKind, items.Content[0].Kind, "output:\n%s", out)
			require.NotEqual(t, "!Widget", items.Content[0].Tag, "output:\n%s", out)
			require.NotContains(t, string(out), "!Widget")
		})
	}
}

func TestSequenceTagIntentTracksEveryShiftedItem(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - !Widget same\n  - !Widget same\n  - same\nkeep: 1\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0"}]`)))
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":"same"}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	items := parsedRootValue(t, out, "items")
	require.Len(t, items.Content, 3, "output:\n%s", out)
	require.Equal(t, "!Widget", items.Content[0].Tag, "output:\n%s", out)
	require.Equal(t, "!!str", items.Content[1].Tag, "output:\n%s", out)
	require.Equal(t, "!!str", items.Content[2].Tag, "output:\n%s", out)
}
