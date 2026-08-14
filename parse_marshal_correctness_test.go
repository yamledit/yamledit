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

func TestParseMarshalPreservesImplicitNullsExactly(t *testing.T) {
	tests := []struct {
		name  string
		input string
	}{
		{name: "block", input: "config:\n"},
		{name: "inline comment", input: "0\": #\n"},
		{name: "root anchor and comments", input: "&000000000 #000000\n00000000A: #000000"},
		{name: "flow collection line comment", input: "00A: &base {0000:00,000A: [A,A]}#00000000"},
		{name: "flow scalar spelling", input: "000A: {1001A: [000,00],00000A: {00000000000A}}#00000000000"},
		{name: "bare non-specific tag", input: "A:\n  - 0000A: !\n  - {A}"},
		{name: "custom tag sibling", input: "container: {target: , sibling: !Custom value}\n"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			before := cloneYAMLNodeGraph(doc)

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, tt.input, string(out))
			require.True(t, yamlNodeGraphEqual(doc, before), "no-op Marshal mutated the YAML graph")

			roundTrip, err := Parse(out)
			require.NoError(t, err)
			require.True(t, yamlNodeGraphEqual(doc, roundTrip), "exact no-op output changed the YAML graph")
		})
	}
}

func TestParseKeepsImplicitNullAsNullNode(t *testing.T) {
	doc, err := Parse([]byte("config:\n"))
	require.NoError(t, err)
	require.Len(t, doc.Content[0].Content, 2)
	value := doc.Content[0].Content[1]
	require.Equal(t, yaml.ScalarNode, value.Kind)
	require.Equal(t, "!!null", value.Tag)
	require.Empty(t, value.Value)
}

func TestEnsurePathExplicitlyConvertsImplicitNullToMapping(t *testing.T) {
	doc, err := Parse([]byte("config:\nsibling: keep\n"))
	require.NoError(t, err)

	config := EnsurePath(doc, "config")
	require.NotNil(t, config)
	require.Equal(t, yaml.MappingNode, config.Kind)
	SetValue(config, "enabled", true, SetValueOptions{})

	out, err := Marshal(doc)
	require.NoError(t, err)
	roundTrip, err := Parse(out)
	require.NoError(t, err, "output:\n%s", out)
	enabled, exists := yamlNodeAtPathSegments(roundTrip.Content[0], []string{"config", "enabled"})
	require.True(t, exists, "output:\n%s", out)
	require.Equal(t, yaml.ScalarNode, enabled.Kind)
	require.Equal(t, "!!bool", enabled.Tag)
	require.Equal(t, "true", enabled.Value)
	sibling, exists := yamlNodeAtPathSegments(roundTrip.Content[0], []string{"sibling"})
	require.True(t, exists, "output:\n%s", out)
	require.Equal(t, "keep", sibling.Value)
}

func TestSetValueReplacesImplicitNullInFlowCollection(t *testing.T) {
	input := []byte("container: {target: , sibling: !Custom value}\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	container := doc.Content[0].Content[1]

	SetValue(container, "target", map[string]any{"nested": true}, SetValueOptions{})

	out, err := Marshal(doc)
	require.NoError(t, err)
	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
	nested, exists := yamlNodeAtPathSegments(reparsed.Content[0], []string{"container", "target", "nested"})
	require.True(t, exists, "output:\n%s", out)
	require.Equal(t, "!!bool", nested.Tag)
	sibling, exists := yamlNodeAtPathSegments(reparsed.Content[0], []string{"container", "sibling"})
	require.True(t, exists, "output:\n%s", out)
	require.Equal(t, "!Custom", sibling.Tag)
}

func TestFlowScalarPatchPreservesImplicitNullSibling(t *testing.T) {
	input := []byte("base: {x: 0,A}")
	doc, err := Parse(input)
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/base/x","value":1}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "base: {x: 1,A}", string(out))

	roundTrip, err := Parse(out)
	require.NoError(t, err)
	nullValue, exists := yamlNodeAtPathSegments(roundTrip.Content[0], []string{"base", "A"})
	require.True(t, exists)
	require.Equal(t, yaml.ScalarNode, nullValue.Kind)
	require.Equal(t, "!!null", nullValue.Tag)
	require.Empty(t, nullValue.Value)
}

func TestFlowExplicitNullReplacementCanRewriteOpaqueSibling(t *testing.T) {
	input := []byte("container: {target: !!null '', sibling: !Custom value}\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	container := doc.Content[0].Content[1]

	SetValue(container, "target", map[string]any{}, SetValueOptions{})
	out, err := Marshal(doc)
	require.NoError(t, err)

	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
	target, exists := yamlNodeAtPathSegments(reparsed.Content[0], []string{"container", "target"})
	require.True(t, exists, "output:\n%s", out)
	require.Equal(t, yaml.MappingNode, target.Kind)
	require.Empty(t, target.Content)
	sibling, exists := yamlNodeAtPathSegments(reparsed.Content[0], []string{"container", "sibling"})
	require.True(t, exists, "output:\n%s", out)
	require.Equal(t, "!Custom", sibling.Tag)
	require.Equal(t, "value", sibling.Value)
}

func TestMappingBoundsKeepOnlyEntryLineCommentMetadata(t *testing.T) {
	source := []byte("outer: # key line\n  nested: value # child line\n")
	var doc yaml.Node
	require.NoError(t, yaml.Unmarshal(source, &doc))
	root := doc.Content[0]
	key, value := root.Content[0], root.Content[1]

	// Model collection metadata attached on a later source line. The entry's
	// own key-line comment wins; without it, the later comment is not hoisted.
	value.LineComment = "# later collection line"
	bounds, _, _ := indexBoundsByPathKeyDeep(source, &doc)
	require.Equal(t, "# key line", bounds[joinPath([]string{"outer"})][0].lineComment)

	key.LineComment = ""
	bounds, _, _ = indexBoundsByPathKeyDeep(source, &doc)
	require.Empty(t, bounds[joinPath([]string{"outer"})][0].lineComment)
}

func TestYAMLCommentScannerDoesNotSplitClosingDelimiterInPlainScalar(t *testing.T) {
	for _, scalar := range []string{"x}#suffix", "x]#suffix"} {
		t.Run(scalar, func(t *testing.T) {
			input := "value: " + scalar + "\n"
			require.Equal(t, -1, yamlCommentStart([]byte(input)))

			doc, err := Parse([]byte(input))
			require.NoError(t, err)
			original := doc.Content[0].Content[1]
			require.Equal(t, yaml.ScalarNode, original.Kind)
			require.Equal(t, scalar, original.Value)
			require.Empty(t, original.LineComment)

			SetValue(doc.Content[0], "value", map[string]any{"nested": true}, SetValueOptions{})
			out, err := Marshal(doc)
			require.NoError(t, err)
			require.NotContains(t, string(out), "#suffix", "plain-scalar content became a comment:\n%s", out)
		})
	}
}

func TestParseRejectsComplexMappingKeys(t *testing.T) {
	_, err := Parse([]byte("? 0:\n"))
	require.ErrorContains(t, err, "complex YAML mapping keys are not supported")

	// Scalar keys with non-string YAML tags remain valid and round-trip exactly.
	doc, err := Parse([]byte("1: integer\n"))
	require.NoError(t, err)
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "1: integer\n", string(out))
}

func TestImplicitNullNoopPreservesMappingKeyAnchor(t *testing.T) {
	input := []byte("&0::")
	doc, err := Parse(input)
	require.NoError(t, err)
	before := cloneYAMLNodeGraph(doc)

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)
	require.True(t, yamlNodeGraphEqual(doc, before), "no-op Marshal mutated the YAML graph")
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

func TestImplicitNullNoopPreservesIndentedComment(t *testing.T) {
	input := []byte("a:\n  # important\nkeep: yes\n")
	doc, err := Parse(input)
	require.NoError(t, err)

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)

	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got))
	require.Nil(t, got["a"])
	require.Equal(t, "yes", got["keep"])
}

func TestDuplicateCleanupDoesNotOverwriteWinningValue(t *testing.T) {
	tests := []struct {
		name  string
		input string
		want  string
		path  []string
	}{
		{
			name:  "direct shadowed null",
			input: "e:\ne: 00 # winning integer\ntail: keep\n",
			want:  "e: 00 # winning integer\ntail: keep\n",
			path:  []string{"e"},
		},
		{
			name:  "null below shadowed ancestor",
			input: "e:\n  nested:\ne:\n  nested: 00 # winning integer\ntail: keep\n",
			want:  "e:\n  nested: 00 # winning integer\ntail: keep\n",
			path:  []string{"e", "nested"},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, tt.want, string(out))

			var reparsed yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &reparsed))
			winning, exists := yamlNodeAtPathSegments(reparsed.Content[0], tt.path)
			require.True(t, exists)
			require.Equal(t, yaml.ScalarNode, winning.Kind)
			require.Equal(t, "!!int", winning.Tag)
			require.Equal(t, "00", winning.Value)
		})
	}
}

func TestParseUsesLiveASTWhenYAMLParsersDisagree(t *testing.T) {
	// goccy/go-yaml accepts this flow spelling as key "0" with a null value,
	// while yaml.v3 (whose public AST Parse returns) reads key "0:". The shadow
	// must follow that live AST or even a no-op Marshal validates against the
	// wrong logical path.
	input := []byte("A: {0:}")
	doc, err := Parse(input)
	require.NoError(t, err)

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)

	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
	value, exists := yamlNodeAtPathSegments(reparsed.Content[0], []string{"A", "0:"})
	require.True(t, exists, "output:\n%s", out)
	require.Equal(t, yaml.ScalarNode, value.Kind)
	require.Equal(t, "!!null", value.Tag)
	require.Empty(t, value.Value)
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
