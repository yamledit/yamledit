package yamledit

import (
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestMarshalHonorsDirectASTScalarMutation(t *testing.T) {
	doc, err := Parse([]byte("a: 1\nkeep: yes\n"))
	require.NoError(t, err)
	value := doc.Content[0].Content[1]
	value.Tag = "!!str"
	value.Value = "2"

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "!!str", scalarForKey(t, out, "a").Tag, "output:\n%s", out)
	require.Equal(t, "2", scalarForKey(t, out, "a").Value)
}

func TestMarshalHonorsDirectASTSequenceMutation(t *testing.T) {
	doc, err := Parse([]byte("arr:\n  - a\n  - b\n"))
	require.NoError(t, err)
	seq := doc.Content[0].Content[1]
	seq.Content = seq.Content[:1]

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string][]string
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, []string{"a"}, got["arr"])
}

func TestMarshalHonorsDirectASTPresentationAndAliasMutations(t *testing.T) {
	t.Run("style only", func(t *testing.T) {
		doc, err := Parse([]byte("a: plain\n"))
		require.NoError(t, err)
		doc.Content[0].Content[1].Style = yaml.DoubleQuotedStyle
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Contains(t, string(out), `a: "plain"`)
	})

	t.Run("custom tag inserted into empty mapping", func(t *testing.T) {
		doc, err := Parse([]byte("{}\n"))
		require.NoError(t, err)
		doc.Content[0].Content = []*yaml.Node{
			{Kind: yaml.ScalarNode, Tag: "!!str", Value: "special"},
			{Kind: yaml.ScalarNode, Tag: "!Widget", Value: "value"},
		}
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, "!Widget", scalarForKey(t, out, "special").Tag, "output:\n%s", out)
	})

	t.Run("alias retarget with equal values", func(t *testing.T) {
		doc, err := Parse([]byte("one: &one x\ntwo: &two x\nref: *one\n"))
		require.NoError(t, err)
		root := doc.Content[0]
		ref := root.Content[5]
		ref.Value = "two"
		ref.Alias = root.Content[3]
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Contains(t, string(out), "ref: *two")
	})
}

func TestMarshalRejectsDirectComplexMappingKeyWithoutSilentLoss(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	complexKey := &yaml.Node{Kind: yaml.SequenceNode, Tag: "!!seq", Content: []*yaml.Node{
		{Kind: yaml.ScalarNode, Tag: "!!str", Value: "k"},
	}}
	doc.Content[0].Content = append(doc.Content[0].Content, complexKey,
		&yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: "v"})

	_, err = Marshal(doc)
	require.ErrorContains(t, err, "non-scalar key")
}

func TestMarshalNoOpPreservesFormattingAcrossParserNumericRepresentations(t *testing.T) {
	inputs := []string{
		"# header\nx: 1.1   # inline\n\nkeep:  yes\n",
		"# header\nbig: 18446744073709551616   # inline\n\nkeep:  yes\n",
		"# header\nbase: &a 1.1   # inline\n\ncopy: *a\n",
	}
	for _, input := range inputs {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, input, string(out))
	}
}

func TestMarshalKeepsDirectPresentationEditMadeBeforeSetter(t *testing.T) {
	doc, err := Parse([]byte("a: plain\nb: old\n"))
	require.NoError(t, err)
	doc.Content[0].Content[1].Style = yaml.DoubleQuotedStyle
	SetScalarString(doc.Content[0], "b", "new")

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), `a: "plain"`)
	require.Equal(t, "new", scalarForKey(t, out, "b").Value)
}
