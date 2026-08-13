package yamledit

import (
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestJSONPatchRejectsReplacementThatWouldDangleAlias(t *testing.T) {
	input := []byte("scope:\n  parent:\n    child: &shared old\nref: *shared\n")
	tests := []struct {
		name  string
		patch string
	}{
		{
			name:  "replace",
			patch: `[{"op":"replace","path":"/parent","value":{"new":1}}]`,
		},
		{
			name:  "add over existing member",
			patch: `[{"op":"add","path":"/parent","value":{"new":1}}]`,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse(input)
			require.NoError(t, err)
			scope := doc.Content[0].Content[1]

			err = ApplyJSONPatchBytes(scope, []byte(tt.patch))
			require.ErrorContains(t, err, "invalid YAML alias")

			out, marshalErr := Marshal(doc)
			require.NoError(t, marshalErr)
			require.Equal(t, input, out)
		})
	}
}

func TestJSONPatchCanReplaceAnchoredNodeWithoutDanglingAlias(t *testing.T) {
	doc, err := Parse([]byte("parent:\n  child: &shared old\nref: *shared\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(
		`[{"op":"replace","path":"/parent/child","value":"new"}]`,
	)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "new", got["parent"].(map[string]any)["child"])
	require.Equal(t, "new", got["ref"])
}

func TestJSONPatchRejectsDuplicateDefinedOperationMembers(t *testing.T) {
	tests := []string{
		`[{"op":"remove","op":"add","path":"/added","value":2}]`,
		`[{"op":"add","path":"/first","path":"/second","value":2}]`,
		`[{"op":"add","path":"/added","value":1,"value":2}]`,
		`[{"op":"copy","from":"/source","from":"/other","path":"/copy"}]`,
	}
	for _, patch := range tests {
		t.Run(patch, func(t *testing.T) {
			input := []byte("source: 1\nother: 2\n")
			doc, err := Parse(input)
			require.NoError(t, err)
			require.ErrorContains(t, ApplyJSONPatchBytes(doc, []byte(patch)), "duplicate member")
			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, input, out)
		})
	}
}

func TestJSONPatchIgnoresDuplicateMembersUndefinedForOperation(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	patch := []byte(`[
		{"op":"remove","path":"/a","value":1,"value":2},
		{"op":"add","path":"/b","from":"/missing","from":"/also-missing","value":3}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, 3, yamlNodeToInterface(scalarForKey(t, out, "b")))
}

func TestJSONPatchTestComparesNumbersWithArbitrarilyLargeExponents(t *testing.T) {
	doc, err := Parse([]byte("keep: true\n"))
	require.NoError(t, err)

	patch := []byte(`[
		{"op":"add","path":"/positive","value":1e9223372036854775808},
		{"op":"test","path":"/positive","value":10e9223372036854775807},
		{"op":"add","path":"/negative","value":10e-9223372036854775809},
		{"op":"test","path":"/negative","value":1e-9223372036854775808}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "positive: !!float 1e9223372036854775808")
	require.Contains(t, string(out), "negative: 10e-9223372036854775809")
}

func TestJSONPatchCopiesDocumentRootToNonRootDestination(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(
		`[{"op":"copy","from":"","path":"/snapshot"}]`,
	)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]any{"a": 1}, got["snapshot"])
}

func TestJSONPatchRootCopyRejectsNonJSONSourceAtomically(t *testing.T) {
	input := []byte("ordinary: 1\nspecial: !Widget value\n")
	doc, err := Parse(input)
	require.NoError(t, err)

	patch := []byte(`[
		{"op":"add","path":"/transient","value":true},
		{"op":"copy","from":"","path":"/snapshot"}
	]`)
	require.ErrorContains(t, ApplyJSONPatchBytes(doc, patch), "source is not JSON-compatible")

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)
}

func TestJSONPatchRootCopyDoesNotEnableOtherRootMutations(t *testing.T) {
	tests := []struct {
		name  string
		patch string
	}{
		{name: "copy to root", patch: `[{"op":"copy","from":"/a","path":""}]`},
		{name: "move from root", patch: `[{"op":"move","from":"","path":"/snapshot"}]`},
		{name: "add root", patch: `[{"op":"add","path":"","value":{"replacement":true}}]`},
		{name: "remove root", patch: `[{"op":"remove","path":""}]`},
		{name: "replace root", patch: `[{"op":"replace","path":"","value":{"replacement":true}}]`},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			input := []byte("a: 1\n")
			doc, err := Parse(input)
			require.NoError(t, err)
			require.Error(t, ApplyJSONPatchBytes(doc, []byte(tt.patch)))
			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, input, out)
		})
	}
}

func TestJSONPatchSequenceScalarSameLexemeTagReplacement(t *testing.T) {
	tests := []struct {
		name  string
		input string
		value string
		want  string
	}{
		{
			name:  "implicit timestamp",
			input: "items:\n  - 2026-07-15 # date\n  - keep\n",
			value: "2026-07-15",
			want:  "items:\n  - \"2026-07-15\" # date\n  - keep\n",
		},
		{
			name:  "custom tag",
			input: "items:\n  - !Widget value # custom\n  - keep\n",
			value: "value",
			want:  "items:\n  - value # custom\n  - keep\n",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(
				`[{"op":"replace","path":"/items/0","value":"`+tt.value+`"}]`,
			)))

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, tt.want, string(out))

			again, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, out, again)

			var reparsed yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
			item := reparsed.Content[0].Content[1].Content[0]
			require.Equal(t, "!!str", item.Tag)
			require.Equal(t, tt.value, item.Value)
		})
	}
}

func TestJSONPatchSequenceScalarSameLexemeRemoveAndReinsert(t *testing.T) {
	tests := []struct {
		name  string
		input string
		value string
		want  string
	}{
		{
			name:  "implicit timestamp",
			input: "items:\n  - 2026-07-15\n  - keep\n",
			value: "2026-07-15",
			want:  "items:\n  - \"2026-07-15\"\n  - keep\n",
		},
		{
			name:  "custom tag",
			input: "items:\n  - !Widget value\n  - keep\n",
			value: "value",
			want:  "items:\n  - value\n  - keep\n",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(
				`[{"op":"remove","path":"/items/0"},{"op":"add","path":"/items/0","value":"`+tt.value+`"}]`,
			)))

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Equal(t, tt.want, string(out))

			var reparsed yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
			item := reparsed.Content[0].Content[1].Content[0]
			require.Equal(t, "!!str", item.Tag)
			require.Equal(t, tt.value, item.Value)
		})
	}
}

func TestJSONPatchRejectsMalformedCallerConstructedASTWithoutPanic(t *testing.T) {
	key := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: "x"}
	tests := []struct {
		name string
		node *yaml.Node
	}{
		{
			name: "document with nil mapping value",
			node: &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{{
				Kind:    yaml.MappingNode,
				Tag:     "!!map",
				Content: []*yaml.Node{key, nil},
			}}},
		},
		{
			name: "standalone mapping with unmatched key",
			node: &yaml.Node{
				Kind:    yaml.MappingNode,
				Tag:     "!!map",
				Content: []*yaml.Node{{Kind: yaml.ScalarNode, Tag: "!!str", Value: "x"}},
			},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			require.NotPanics(t, func() {
				err := ApplyJSONPatchBytes(test.node, []byte(`[{
					"op":"replace","path":"/x","value":1
				}]`))
				require.ErrorContains(t, err, "malformed YAML")
			})
		})
	}
}

func TestJSONPatchRejectsMalformedDirectEditAtomically(t *testing.T) {
	input := []byte("x: old\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	doc.Content[0].Content[1] = nil

	require.NotPanics(t, func() {
		err = ApplyJSONPatchBytes(doc, []byte(`[{
			"op":"replace","path":"/x","value":"new"
		}]`))
	})
	require.ErrorContains(t, err, "malformed YAML")
	require.Nil(t, doc.Content[0].Content[1], "a rejected patch must not repair or partially mutate the caller's AST")
}
