package yamledit

import (
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestSetValueHandlesCyclicCallerValues(t *testing.T) {
	t.Run("self-referential mapping", func(t *testing.T) {
		value := map[string]any{}
		value["self"] = value

		doc, err := Parse([]byte("value: old\ntail: keep\n"))
		require.NoError(t, err)
		require.NotPanics(t, func() {
			SetValue(doc.Content[0], "value", value, SetValueOptions{SortKeys: true})
		})

		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Contains(t, string(out), "tail: keep")
		var round yaml.Node
		require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
		got := mappingValueForStringKey(t, round.Content[0], "value")
		require.Equal(t, yaml.MappingNode, got.Kind, "output:\n%s", out)
		require.Equal(t, setValueCycleMarker, mappingValueForStringKey(t, got, "self").Value)
	})

	t.Run("self-referential sequence", func(t *testing.T) {
		value := make([]any, 1)
		value[0] = value

		doc, err := Parse([]byte("value: old\n"))
		require.NoError(t, err)
		require.NotPanics(t, func() {
			SetValue(doc.Content[0], "value", value, SetValueOptions{})
		})

		out, err := Marshal(doc)
		require.NoError(t, err)
		var round yaml.Node
		require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
		got := mappingValueForStringKey(t, round.Content[0], "value")
		require.Equal(t, yaml.SequenceNode, got.Kind, "output:\n%s", out)
		require.Len(t, got.Content, 1)
		require.Equal(t, setValueCycleMarker, got.Content[0].Value)
	})

	t.Run("mutually recursive mappings", func(t *testing.T) {
		left := map[string]any{}
		right := map[string]any{}
		left["right"] = right
		right["left"] = left

		doc, err := Parse([]byte("value: old\n"))
		require.NoError(t, err)
		require.NotPanics(t, func() {
			SetValue(doc.Content[0], "value", left, SetValueOptions{SortKeys: true})
		})

		out, err := Marshal(doc)
		require.NoError(t, err)
		var round yaml.Node
		require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
		got := mappingValueForStringKey(t, round.Content[0], "value")
		got = mappingValueForStringKey(t, got, "right")
		require.Equal(t, setValueCycleMarker, mappingValueForStringKey(t, got, "left").Value)
	})
}

func TestSetValueBoundsCallerCollectionGraphs(t *testing.T) {
	t.Run("excessive nesting", func(t *testing.T) {
		value := any("unreachable leaf")
		for range setValueMaxNestingDepth + 1 {
			value = []any{value}
		}

		doc, err := Parse([]byte("value: old\n"))
		require.NoError(t, err)
		require.NotPanics(t, func() {
			SetValue(doc.Content[0], "value", value, SetValueOptions{})
		})
		out, err := Marshal(doc)
		require.NoError(t, err)

		var round yaml.Node
		require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
		got := mappingValueForStringKey(t, round.Content[0], "value")
		for depth := 0; depth < setValueMaxNestingDepth; depth++ {
			require.Equal(t, yaml.SequenceNode, got.Kind, "depth %d; output:\n%s", depth, out)
			require.Len(t, got.Content, 1, "depth %d; output:\n%s", depth, out)
			got = got.Content[0]
		}
		require.Equal(t, yaml.ScalarNode, got.Kind, "output:\n%s", out)
		require.Equal(t, setValueDepthMarker, got.Value)
	})

	t.Run("node budget", func(t *testing.T) {
		value := make([]any, setValueNodeBudget+1)
		doc, err := Parse([]byte("value: old\n"))
		require.NoError(t, err)
		require.NotPanics(t, func() {
			SetValue(doc.Content[0], "value", value, SetValueOptions{})
		})

		out, err := Marshal(doc)
		require.NoError(t, err)
		var round yaml.Node
		require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
		got := mappingValueForStringKey(t, round.Content[0], "value")
		require.Equal(t, yaml.ScalarNode, got.Kind, "output:\n%s", out)
		require.Equal(t, setValueSizeMarker, got.Value)
	})
}

func TestSetValueDoesNotTreatSharedAcyclicContainersAsCycles(t *testing.T) {
	shared := map[string]any{"number": int8(7)}
	doc, err := Parse([]byte("value: old\n"))
	require.NoError(t, err)
	SetValue(doc.Content[0], "value", []any{shared, shared}, SetValueOptions{SortKeys: true})

	out, err := Marshal(doc)
	require.NoError(t, err)
	var round yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
	got := mappingValueForStringKey(t, round.Content[0], "value")
	require.Equal(t, yaml.SequenceNode, got.Kind, "output:\n%s", out)
	require.Len(t, got.Content, 2)
	for _, item := range got.Content {
		require.Equal(t, yaml.MappingNode, item.Kind, "output:\n%s", out)
		number := mappingValueForStringKey(t, item, "number")
		require.Equal(t, "!!int", number.Tag)
		require.Equal(t, "7", number.Value)
	}
}
