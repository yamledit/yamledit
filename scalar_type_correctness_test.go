package yamledit

import (
	"math"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func scalarForKey(t *testing.T, data []byte, key string) *yaml.Node {
	t.Helper()
	var doc yaml.Node
	require.NoError(t, yaml.Unmarshal(data, &doc), "output:\n%s", data)
	root := doc.Content[0]
	for i := 0; i+1 < len(root.Content); i += 2 {
		if root.Content[i].Value == key {
			return root.Content[i+1]
		}
	}
	t.Fatalf("key %q not found in output:\n%s", key, data)
	return nil
}

func TestScalarSettersPreserveRequestedYAMLType(t *testing.T) {
	tests := []struct {
		name  string
		input string
		edit  func(*yaml.Node)
		tag   string
	}{
		{
			name:  "integer to float",
			input: "x: 1\n",
			edit:  func(root *yaml.Node) { SetScalarFloat(root, "x", 1.0) },
			tag:   "!!float",
		},
		{
			name:  "float to integer",
			input: "x: 1.0\n",
			edit:  func(root *yaml.Node) { SetScalarInt(root, "x", 1) },
			tag:   "!!int",
		},
		{
			name:  "integer to negative zero float",
			input: "x: 0\n",
			edit:  func(root *yaml.Node) { SetScalarFloat(root, "x", math.Copysign(0, -1)) },
			tag:   "!!float",
		},
		{
			name:  "positive float zero to negative float zero",
			input: "x: 0.0\n",
			edit:  func(root *yaml.Node) { SetScalarFloat(root, "x", math.Copysign(0, -1)) },
			tag:   "!!float",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			tt.edit(doc.Content[0])
			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, tt.tag, scalarForKey(t, out, "x").Tag, "output:\n%s", out)
			if tt.name == "positive float zero to negative float zero" {
				require.Equal(t, "-0.0", scalarForKey(t, out, "x").Value, "output:\n%s", out)
			}
		})
	}
}

func TestStringSetterDoesNotKeepBareNonStringToken(t *testing.T) {
	doc, err := Parse([]byte("x: 1\nother: old\n"))
	require.NoError(t, err)
	root := doc.Content[0]
	SetScalarString(root, "x", "1")
	SetScalarString(root, "other", "new")

	out, err := Marshal(doc)
	require.NoError(t, err)
	x := scalarForKey(t, out, "x")
	require.Equal(t, "!!str", x.Tag, "output:\n%s", out)
	require.Equal(t, "1", x.Value)
}

func TestStringSetterRemovesSameLexemeYAMLOnlyTag(t *testing.T) {
	inputs := []string{
		"date: 2026-07-15\nkeep: yes\n",
		"date: !Widget 2026-07-15\nkeep: yes\n",
	}
	for _, input := range inputs {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		SetScalarString(doc.Content[0], "date", "2026-07-15")
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, "!!str", scalarForKey(t, out, "date").Tag, "output:\n%s", out)
	}
}

func TestJSONPatchRemovesSameLexemeYAMLOnlyTag(t *testing.T) {
	for _, op := range []string{"add", "replace"} {
		doc, err := Parse([]byte("date: !Widget 2026-07-15\nkeep: yes\n"))
		require.NoError(t, err)
		patch := `[{"op":"` + op + `","path":"/date","value":"2026-07-15"}]`
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(patch)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, "!!str", scalarForKey(t, out, "date").Tag, "output:\n%s", out)
	}
}

func TestScalarTagRewriteIntentTracksFinalSequentialValue(t *testing.T) {
	t.Run("setter", func(t *testing.T) {
		doc, err := Parse([]byte("date: !Widget value\n"))
		require.NoError(t, err)
		SetScalarString(doc.Content[0], "date", "value")
		SetScalarInt(doc.Content[0], "date", 2)
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, "!!int", scalarForKey(t, out, "date").Tag, "output:\n%s", out)
	})

	t.Run("json patch", func(t *testing.T) {
		doc, err := Parse([]byte("date: !Widget value\n"))
		require.NoError(t, err)
		patch := []byte(`[
			{"op":"replace","path":"/date","value":"value"},
			{"op":"replace","path":"/date","value":2}
		]`)
		require.NoError(t, ApplyJSONPatchBytes(doc, patch))
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, "!!int", scalarForKey(t, out, "date").Tag, "output:\n%s", out)
	})
}

func TestJSONPatchReplacePreservesRequestedNumberCategory(t *testing.T) {
	doc, err := Parse([]byte("x: 1\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/x","value":1.0}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "!!float", scalarForKey(t, out, "x").Tag, "output:\n%s", out)
}

func TestJSONPatchHugeNumberReplacementUsesOneExplicitTag(t *testing.T) {
	tests := []struct {
		name  string
		input string
		path  string
		value func(*yaml.Node) *yaml.Node
	}{
		{
			name:  "mapping implicit tag",
			input: "n: 1.0\n",
			path:  "/n",
			value: func(doc *yaml.Node) *yaml.Node { return doc.Content[0].Content[1] },
		},
		{
			name:  "mapping compatible explicit tag",
			input: "n: !!float 1.0\n",
			path:  "/n",
			value: func(doc *yaml.Node) *yaml.Node { return doc.Content[0].Content[1] },
		},
		{
			name:  "named sequence mapping implicit tag",
			input: "items:\n  - name: item\n    n: 1.0\n",
			path:  "/items/0/n",
			value: func(doc *yaml.Node) *yaml.Node { return doc.Content[0].Content[1].Content[0].Content[3] },
		},
		{
			name:  "named sequence mapping compatible explicit tag",
			input: "items:\n  - name: item\n    n: !!float 1.0\n",
			path:  "/items/0/n",
			value: func(doc *yaml.Node) *yaml.Node { return doc.Content[0].Content[1].Content[0].Content[3] },
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"`+tt.path+`","value":1e999}]`)))

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, 1, strings.Count(string(out), "!!float"), "output:\n%s", out)

			var parsed yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &parsed), "output:\n%s", out)
			value := tt.value(&parsed)
			require.Equal(t, "!!float", value.Tag, "output:\n%s", out)
			require.Equal(t, "1e999", value.Value, "output:\n%s", out)
		})
	}
}
