package yamledit

import (
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestStructuralRewriteConsumesMultilineDelimitedValue(t *testing.T) {
	tests := []struct {
		name  string
		input string
		patch string
		want  map[string]any
	}{
		{
			name:  "flow mapping continuation at column one",
			input: "flow: {a: 1,\nb: 2}\nkeep: yes\n",
			patch: `[{"op":"replace","path":"/flow/a","value":3}]`,
			want: map[string]any{
				"flow": map[string]any{"a": 3, "b": 2},
				"keep": "yes",
			},
		},
		{
			name:  "flow mapping nested in block sequence",
			input: "items:\n  - {a: 1,\nfake: two}\nkeep: yes\n",
			patch: `[{"op":"replace","path":"/items/0/a","value":3}]`,
			want: map[string]any{
				"items": []any{map[string]any{"a": 3, "fake": "two"}},
				"keep":  "yes",
			},
		},
		{
			name:  "quoted scalar nested in block sequence",
			input: "items:\n  - \"old\nfoo: bar\"\nkeep: yes\n",
			patch: `[{"op":"replace","path":"/items/0","value":"new"}]`,
			want: map[string]any{
				"items": []any{"new"},
				"keep":  "yes",
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(tt.patch)))

			out, err := Marshal(doc)
			require.NoError(t, err)
			var got map[string]any
			require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
			require.Equal(t, tt.want, got, "output:\n%s", out)
		})
	}
}

func TestAnchoredCollectionEditKeepsAliasSyntax(t *testing.T) {
	input := []byte("base: &base {x: 1}\ncopy: *base\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/base/x","value":2}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "copy: *base")

	var parsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &parsed), "output:\n%s", out)
	root := parsed.Content[0]
	require.Len(t, root.Content, 4)
	base, alias := root.Content[1], root.Content[3]
	require.Equal(t, "base", base.Anchor, "output:\n%s", out)
	require.Equal(t, yaml.AliasNode, alias.Kind, "output:\n%s", out)
	require.Same(t, base, alias.Alias, "output:\n%s", out)
	require.Equal(t, "2", base.Content[1].Value, "output:\n%s", out)
}

func TestSequenceRewriteKeepsWholeMultilinePlainScalar(t *testing.T) {
	input := []byte("items:\n  - first line\n    continuation\n  - keep\n")
	for _, index := range []string{"0", "1"} {
		t.Run("remove index "+index, func(t *testing.T) {
			doc, err := Parse(input)
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/`+index+`"}]`)))
			out, err := Marshal(doc)
			require.NoError(t, err)
			var got map[string][]string
			require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
			if index == "0" {
				require.Equal(t, []string{"keep"}, got["items"])
			} else {
				require.Equal(t, []string{"first line continuation"}, got["items"])
			}
		})
	}
}

func TestSequenceRewriteKeepsPlainScalarAfterMultilineTagProperty(t *testing.T) {
	input := []byte("items:\n  - !!str\n    plain\n  - keep\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/1"}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string][]string
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, []string{"plain"}, got["items"])
	require.Contains(t, string(out), "- !!str\n    plain")
}

func TestMappingInsertionFollowsMultilineLastValue(t *testing.T) {
	tests := []struct {
		name  string
		input string
		want  any
	}{
		{
			name:  "plain scalar",
			input: "obj:\n  x: old\n    continued\n",
			want:  "old continued",
		},
		{
			name:  "single quoted scalar",
			input: "obj:\n  x: 'old\n    continued'\n",
			want:  "old continued",
		},
		{
			name:  "double quoted scalar",
			input: "obj:\n  x: \"old\n    continued\"\n",
			want:  "old continued",
		},
		{
			name:  "flow sequence",
			input: "obj:\n  x: [one,\ntwo]\n",
			want:  []any{"one", "two"},
		},
		{
			name:  "flow mapping",
			input: "obj:\n  x: {a: 1,\nb: 2}\n",
			want:  map[string]any{"a": 1, "b": 2},
		},
		{
			name:  "flow collection after anchor property",
			input: "obj:\n  x: &held {a: 1,\nb: [2, 3]}\n",
			want:  map[string]any{"a": 1, "b": []any{2, 3}},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/obj/new","value":1}]`)))

			out, err := Marshal(doc)
			require.NoError(t, err)
			var got map[string]map[string]any
			require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
			require.Equal(t, tt.want, got["obj"]["x"], "output:\n%s", out)
			require.Equal(t, 1, got["obj"]["new"], "output:\n%s", out)
		})
	}
}

func TestSequenceItemMappingInsertionPreservesMultilineSibling(t *testing.T) {
	tests := []struct {
		name  string
		input string
	}{
		{
			name:  "ordinary item",
			input: "items:\n  - id: first\n    x: old\n",
		},
		{
			name:  "multiline quoted sibling",
			input: "items:\n  - id: first\n    x: 'single\n      continuation'\n",
		},
		{
			name:  "block scalar sibling",
			input: "items:\n  - id: first\n    x: |\n      line one\n      line two\n",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/0/new","value":1}]`)))

			out, err := Marshal(doc)
			require.NoError(t, err)
			var got map[string][]map[string]any
			require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
			require.Equal(t, 1, got["items"][0]["new"], "output:\n%s", out)
			require.Contains(t, string(out), "    new: 1\n")
			if tt.name == "multiline quoted sibling" {
				require.Contains(t, string(out), "x: 'single\n      continuation'")
			}
			if tt.name == "block scalar sibling" {
				require.Contains(t, string(out), "x: |\n      line one\n      line two")
			}
		})
	}
}

func TestMarshalRejectsMissingLiveRootWithoutPanic(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	doc.Content = nil

	require.NotPanics(t, func() {
		_, err = Marshal(doc)
	})
	require.ErrorContains(t, err, "exactly one YAML root")
}

func TestMarshalRejectsMalformedLiveMappingWithoutPanic(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	doc.Content[0].Content = doc.Content[0].Content[:1]

	require.NotPanics(t, func() {
		_, err = Marshal(doc)
	})
	require.ErrorContains(t, err, "malformed YAML mapping node")
}

func TestImplicitEmptyMapNormalizationPreservesIndentedComment(t *testing.T) {
	input := []byte("a:\n  # important\nkeep: yes\n")
	doc, err := Parse(input)
	require.NoError(t, err)

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "a: {}\n  # important\nkeep: yes\n", string(out))

	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got))
	require.Equal(t, map[string]any{}, got["a"])
	require.Equal(t, "yes", got["keep"])
}

func TestMarshalHonorsDirectAliasInsertionIntoEmptySource(t *testing.T) {
	for _, input := range []string{"# header\n", "{}\n"} {
		t.Run(input, func(t *testing.T) {
			doc, err := Parse([]byte(input))
			require.NoError(t, err)
			anchor := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: "x", Anchor: "base"}
			alias := &yaml.Node{Kind: yaml.AliasNode, Value: "base", Alias: anchor}
			doc.Content[0].Content = []*yaml.Node{
				{Kind: yaml.ScalarNode, Tag: "!!str", Value: "base"}, anchor,
				{Kind: yaml.ScalarNode, Tag: "!!str", Value: "copy"}, alias,
			}

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Contains(t, string(out), "copy: *base")
			if input[0] == '#' {
				require.Contains(t, string(out), "# header")
			}

			var roundTrip yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &roundTrip))
			root := roundTrip.Content[0]
			require.Equal(t, yaml.AliasNode, root.Content[3].Kind)
			require.Same(t, root.Content[1], root.Content[3].Alias)
		})
	}
}
