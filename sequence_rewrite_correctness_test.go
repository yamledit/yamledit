package yamledit

import (
	"bytes"
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestSequenceDeletionWithAmbiguousDuplicatePresentationFailsSafely(t *testing.T) {
	tests := []struct {
		name  string
		input string
	}{
		{
			name:  "different comments",
			input: "items:\n  - same # first\n  - same # second\n  - keep\n",
		},
		{
			name:  "different quote styles",
			input: "items:\n  - 'same'\n  - \"same\"\n  - keep\n",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{
				"op":"remove","path":"/items/0"
			}]`)))

			// The logical shadow contains one "same" item but cannot identify
			// whether its bytes came from index 0 or 1. Returning an error is safer
			// than silently retaining the removed occurrence's presentation.
			_, err = Marshal(doc)
			require.Error(t, err)
		})
	}
}

func TestSequenceDeletionPreservesEmptyScalarPresentation(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - remove\n  - '' # blank-comment\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "items:\n  - '' # blank-comment\n", string(out))
}

func TestSequenceDeletionPreservesEmptyNamePresentation(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - name: remove\n    value: gone\n  - name: '' # empty-name-comment\n    value: keep\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0"}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "items:\n  - name: '' # empty-name-comment\n    value: keep\n", string(out))
}

func TestSequenceDeletionDoesNotResurrectDuplicateIdentityComment(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - name: same\n    value: keep\n  # belongs to removed item\n  - name: same\n    value: remove\n  - name: other\n    value: stay\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{
		"op":"remove","path":"/items/1"
	}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.NotContains(t, string(out), "belongs to removed item")
	require.Equal(t, "items:\n  - name: same\n    value: keep\n  - name: other\n    value: stay\n", string(out))
}

func TestWholeSequenceRewriteSkipsStaleDescendantScalarChecks(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - name: remove\n    value: !!int 1\n  - name: keep # retain\n    value: text\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{
		"op":"remove","path":"/items/0"
	}]`)))

	// Once the block patch has matched and reused the surviving item, descendant
	// scalar surgery must not compare it to the removed item formerly at index 0.
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "items:\n  - name: keep # retain\n    value: text\n", string(out))
}

func TestSequenceAppendPreservesAliasValuedOriginalItem(t *testing.T) {
	input := "base: &base\n  a: 1\nitems:\n  - value: *base\n"
	doc, err := Parse([]byte(input))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":{"new":1}}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input+"  - new: 1\n", string(out))

	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed))
	require.NoError(t, validateYAMLAliasGraph(&reparsed))
	require.Equal(t, yaml.AliasNode, reparsed.Content[0].Content[3].Content[0].Content[1].Kind)
}

func TestSequenceAppendDoesNotReplayDuplicateTemplateKeys(t *testing.T) {
	input := "items:\n  - name: one\n    value: first # first\n    value: second # second\n"
	doc, err := Parse([]byte(input))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":{"name":"two","value":"added"}}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, 1, bytes.Count(out, []byte("value: added")), "output:\n%s", out)

	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed))
	items := reparsed.Content[0].Content[1]
	require.Len(t, items.Content, 2)
	appended := items.Content[1]
	require.Equal(t, yaml.MappingNode, appended.Kind)
	valueKeys := 0
	for i := 0; i < len(appended.Content); i += 2 {
		if appended.Content[i].Value == "value" {
			valueKeys++
		}
	}
	require.Equal(t, 1, valueKeys, "output:\n%s", out)
}
