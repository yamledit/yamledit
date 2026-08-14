package yamledit

import (
	"encoding/json"
	"math"
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

type unsupportedSetValue struct {
	text string
}

func TestSetValueUsesTheSameScalarTypeAtEveryDepth(t *testing.T) {
	tests := []struct {
		name      string
		value     any
		wantTag   string
		wantValue string
	}{
		{name: "int", value: int(7), wantTag: "!!int", wantValue: "7"},
		{name: "int8", value: int8(-8), wantTag: "!!int", wantValue: "-8"},
		{name: "int16", value: int16(-16), wantTag: "!!int", wantValue: "-16"},
		{name: "int32", value: int32(-32), wantTag: "!!int", wantValue: "-32"},
		{name: "int64", value: int64(-64), wantTag: "!!int", wantValue: "-64"},
		{name: "uint", value: uint(7), wantTag: "!!int", wantValue: "7"},
		{name: "uint8", value: uint8(8), wantTag: "!!int", wantValue: "8"},
		{name: "uint16", value: uint16(16), wantTag: "!!int", wantValue: "16"},
		{name: "uint32", value: uint32(32), wantTag: "!!int", wantValue: "32"},
		{name: "uint64", value: uint64(math.MaxUint64), wantTag: "!!int", wantValue: "18446744073709551615"},
		{name: "uintptr", value: uintptr(64), wantTag: "!!int", wantValue: "64"},
		{name: "integral float32", value: float32(4), wantTag: "!!float", wantValue: "4.0"},
		{name: "integral float64", value: float64(4), wantTag: "!!float", wantValue: "4.0"},
		{name: "negative zero float", value: math.Copysign(0, -1), wantTag: "!!float", wantValue: "-0.0"},
		{name: "JSON integer", value: json.Number("9007199254740993"), wantTag: "!!int", wantValue: "9007199254740993"},
		{name: "JSON float", value: json.Number("9007199254740993.0"), wantTag: "!!float", wantValue: "9007199254740993.0"},
		{name: "invalid JSON number", value: json.Number("1 # data"), wantTag: "!!str", wantValue: "1 # data"},
		{name: "bool", value: true, wantTag: "!!bool", wantValue: "true"},
		{name: "string", value: "7", wantTag: "!!str", wantValue: "7"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte("direct: old # retain\nnested: old\nsequence: old\n"))
			require.NoError(t, err)
			root := doc.Content[0]

			SetValue(root, "direct", tt.value, SetValueOptions{})
			SetValue(root, "nested", map[string]any{"value": tt.value}, SetValueOptions{})
			SetValue(root, "sequence", []any{tt.value}, SetValueOptions{})

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Contains(t, string(out), "# retain")

			var round yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
			mapping := round.Content[0]
			direct := mappingValueForStringKey(t, mapping, "direct")
			nested := mappingValueForStringKey(t, mappingValueForStringKey(t, mapping, "nested"), "value")
			sequence := mappingValueForStringKey(t, mapping, "sequence")
			require.Equal(t, yaml.SequenceNode, sequence.Kind, "output:\n%s", out)
			require.Len(t, sequence.Content, 1, "output:\n%s", out)

			for _, node := range []*yaml.Node{direct, nested, sequence.Content[0]} {
				require.Equal(t, yaml.ScalarNode, node.Kind, "output:\n%s", out)
				require.Equal(t, tt.wantTag, node.Tag, "output:\n%s", out)
				require.Equal(t, tt.wantValue, node.Value, "output:\n%s", out)
			}
		})
	}
}

func TestSetValueMarksUnsupportedTypesAtEveryDepth(t *testing.T) {
	doc, err := Parse([]byte("{}\n"))
	require.NoError(t, err)
	root := doc.Content[0]
	unsupported := unsupportedSetValue{text: "must not be stringified"}

	SetValue(root, "direct", unsupported, SetValueOptions{})
	SetValue(root, "nested", map[string]any{"value": unsupported}, SetValueOptions{})
	SetValue(root, "sequence", []any{unsupported}, SetValueOptions{})

	out, err := Marshal(doc)
	require.NoError(t, err)
	var round yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
	parsedRoot := round.Content[0]

	direct := mappingValueForStringKey(t, parsedRoot, "direct")
	require.Equal(t, "!!str", direct.Tag)
	require.Equal(t, setValueTypeMarker, direct.Value)

	nested := mappingValueForStringKey(t, parsedRoot, "nested")
	nestedValue := mappingValueForStringKey(t, nested, "value")
	require.Equal(t, "!!str", nestedValue.Tag)
	require.Equal(t, setValueTypeMarker, nestedValue.Value)

	sequence := mappingValueForStringKey(t, parsedRoot, "sequence")
	require.Len(t, sequence.Content, 1)
	require.Equal(t, "!!str", sequence.Content[0].Tag)
	require.Equal(t, setValueTypeMarker, sequence.Content[0].Value)
}

func TestSetValueWritesEmptyCollectionsAndReplacesMappings(t *testing.T) {
	doc, err := Parse([]byte("emptyAny: old\nemptyStrings: old\nemptyMap:\n  stale: true\nreplacement:\n  stale: true\ndeleteMe: old\nemptyString: old\n"))
	require.NoError(t, err)
	root := doc.Content[0]

	SetValue(root, "emptyAny", []any{}, SetValueOptions{})
	SetValue(root, "emptyStrings", []string{}, SetValueOptions{})
	SetValue(root, "emptyMap", map[string]any{}, SetValueOptions{})
	SetValue(root, "replacement", map[string]any{"new": int8(1)}, SetValueOptions{})
	SetValue(root, "deleteMe", nil, SetValueOptions{})
	SetValue(root, "emptyString", "", SetValueOptions{DeleteEmptyStrings: true})

	out, err := Marshal(doc)
	require.NoError(t, err)
	var round yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
	mapping := round.Content[0]

	for _, key := range []string{"emptyAny", "emptyStrings"} {
		node := mappingValueForStringKey(t, mapping, key)
		require.Equal(t, yaml.SequenceNode, node.Kind, "output:\n%s", out)
		require.Empty(t, node.Content, "output:\n%s", out)
	}
	emptyMap := mappingValueForStringKey(t, mapping, "emptyMap")
	require.Equal(t, yaml.MappingNode, emptyMap.Kind, "output:\n%s", out)
	require.Empty(t, emptyMap.Content, "output:\n%s", out)
	replacement := mappingValueForStringKey(t, mapping, "replacement")
	require.Equal(t, yaml.MappingNode, replacement.Kind, "output:\n%s", out)
	require.Len(t, replacement.Content, 2, "SetValue must replace, rather than merge, a mapping; output:\n%s", out)
	require.Equal(t, "new", replacement.Content[0].Value)
	require.Equal(t, "!!int", replacement.Content[1].Tag)

	for _, key := range []string{"deleteMe", "emptyString"} {
		for i := 0; i+1 < len(mapping.Content); i += 2 {
			require.NotEqual(t, key, mapping.Content[i].Value, "output:\n%s", out)
		}
	}
}

func TestSetValueWholeMappingReplacementHonorsSortedOrder(t *testing.T) {
	doc, err := Parse([]byte("resources:\n  requests:\n    memory: old\n    cpu: old\n  limits:\n    memory: old\n    cpu: old\ntail: yes\n"))
	require.NoError(t, err)

	SetValue(doc.Content[0], "resources", map[string]any{
		"requests": map[string]any{"memory": "512Mi", "cpu": "500m"},
		"limits":   map[string]any{"memory": "1Gi", "cpu": "2"},
	}, SetValueOptions{SortKeys: true})

	out, err := Marshal(doc)
	require.NoError(t, err)
	var round yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
	root := round.Content[0]
	require.Equal(t, "resources", root.Content[0].Value, "replacement keeps its root position; output:\n%s", out)
	require.Equal(t, "tail", root.Content[2].Value, "output:\n%s", out)
	resources := root.Content[1]
	require.Equal(t, []string{"limits", "requests"}, []string{
		resources.Content[0].Value,
		resources.Content[2].Value,
	}, "SortKeys order must govern the entire replacement; output:\n%s", out)
	for index := 1; index < len(resources.Content); index += 2 {
		child := resources.Content[index]
		require.Equal(t, []string{"cpu", "memory"}, []string{
			child.Content[0].Value,
			child.Content[2].Value,
		}, "nested replacement order; output:\n%s", out)
	}
}

func TestSetValueKeepsExactScalarTypeInsideExistingSequenceMapping(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - uint: old # uint comment\n    number: old # number comment\n    float: old # float comment\n"))
	require.NoError(t, err)
	item := mappingValueForStringKey(t, doc.Content[0], "items").Content[0]

	SetValue(item, "uint", uint64(math.MaxUint64), SetValueOptions{})
	SetValue(item, "number", json.Number("1e999"), SetValueOptions{})
	SetValue(item, "float", float64(4), SetValueOptions{})

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "# uint comment")
	require.Contains(t, string(out), "# number comment")
	require.Contains(t, string(out), "# float comment")
	var round yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
	roundItem := mappingValueForStringKey(t, round.Content[0], "items").Content[0]

	uintNode := mappingValueForStringKey(t, roundItem, "uint")
	require.Equal(t, "!!int", uintNode.Tag, "output:\n%s", out)
	require.Equal(t, "18446744073709551615", uintNode.Value)
	numberNode := mappingValueForStringKey(t, roundItem, "number")
	require.Equal(t, "!!float", numberNode.Tag, "output:\n%s", out)
	require.Equal(t, "1e999", numberNode.Value)
	floatNode := mappingValueForStringKey(t, roundItem, "float")
	require.Equal(t, "!!float", floatNode.Tag, "output:\n%s", out)
	require.Equal(t, "4.0", floatNode.Value)
}

func TestSetValueUpdatesWideIntegersInExistingMappings(t *testing.T) {
	t.Run("root", func(t *testing.T) {
		doc, err := Parse([]byte("root: 1 # root comment\n"))
		require.NoError(t, err)
		SetValue(doc.Content[0], "root", uint64(math.MaxUint64), SetValueOptions{})
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Contains(t, string(out), "# root comment")
		require.Equal(t, "18446744073709551615", scalarForKey(t, out, "root").Value)
	})

	t.Run("sequence item mapping", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - value: 2 # item comment\n"))
		require.NoError(t, err)
		item := mappingValueForStringKey(t, doc.Content[0], "items").Content[0]
		SetValue(item, "value", int64(math.MinInt64), SetValueOptions{})
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Contains(t, string(out), "# item comment")
		var round yaml.Node
		require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
		roundItem := mappingValueForStringKey(t, round.Content[0], "items").Content[0]
		require.Equal(t, "-9223372036854775808", mappingValueForStringKey(t, roundItem, "value").Value)
	})
}

func TestSetValueAppliesMapFieldOmissionsRecursively(t *testing.T) {
	doc, err := Parse(nil)
	require.NoError(t, err)

	SetValue(doc.Content[0], "value", map[string]any{
		"keep": "yes",
		"nested": map[string]any{
			"empty": " \t",
			"nil":   nil,
			"value": "kept",
		},
		"sequence": []any{map[string]any{"empty": "", "nil": nil, "value": "kept"}, nil, ""},
	}, SetValueOptions{DeleteEmptyStrings: true, SortKeys: true})

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	value := got["value"].(map[string]any)
	nested := value["nested"].(map[string]any)
	require.Equal(t, map[string]any{"value": "kept"}, nested)
	sequence := value["sequence"].([]any)
	require.Equal(t, map[string]any{"value": "kept"}, sequence[0])
	require.Nil(t, sequence[1], "nil sequence elements are values, not mapping-field deletions")
	require.Equal(t, "", sequence[2], "DeleteEmptyStrings does not remove positional sequence elements")
}

func TestSetValueDoesNotPanicOnNilMappingValueNode(t *testing.T) {
	mapping := &yaml.Node{
		Kind: yaml.MappingNode,
		Tag:  "!!map",
		Content: []*yaml.Node{
			{Kind: yaml.ScalarNode, Tag: "!!str", Value: "value"},
			nil,
		},
	}

	require.NotPanics(t, func() {
		SetValue(mapping, "value", uint64(math.MaxUint64), SetValueOptions{})
	})
	value := mappingValueForStringKey(t, mapping, "value")
	require.Equal(t, "!!int", value.Tag)
	require.Equal(t, "18446744073709551615", value.Value)
}

func TestSetValueMovesScalarInlineCommentToBlockCollectionKey(t *testing.T) {
	doc, err := Parse([]byte("target: old # keep\ntail: yes\n"))
	require.NoError(t, err)
	root := doc.Content[0]

	SetValue(root, "target", map[string]any{"nested": []any{1}}, SetValueOptions{SortKeys: true})
	require.Equal(t, "# keep", root.Content[0].LineComment)
	require.Empty(t, root.Content[1].LineComment)

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "target: # keep\n")
	var reparsed yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
	require.Equal(t, "# keep", reparsed.Content[0].Content[0].LineComment)
	require.Empty(t, reparsed.Content[0].Content[1].LineComment)
}

func TestSetValueCollectionReplacementPreservesAnchoredNodeAndExternalAliases(t *testing.T) {
	tests := []struct {
		name        string
		input       string
		value       any
		wantKind    yaml.Kind
		wantTag     string
		wantContent int
	}{
		{
			name:        "scalar to empty sequence",
			input:       "value: &shared old # keep anchor comment\nalias: *shared\ntail: keep\n",
			value:       []any{},
			wantKind:    yaml.SequenceNode,
			wantTag:     "!!seq",
			wantContent: 0,
		},
		{
			name:        "scalar to mapping",
			input:       "value: &shared old # keep anchor comment\nalias: *shared\ntail: keep\n",
			value:       map[string]any{"new": int8(1)},
			wantKind:    yaml.MappingNode,
			wantTag:     "!!map",
			wantContent: 2,
		},
		{
			name:        "custom sequence to mapping",
			input:       "value: &shared !Widget [old] # keep anchor comment\nalias: *shared\ntail: keep\n",
			value:       map[string]any{"new": true},
			wantKind:    yaml.MappingNode,
			wantTag:     "!!map",
			wantContent: 2,
		},
		{
			name:        "mapping to sequence",
			input:       "value: &shared {old: true} # keep anchor comment\nalias: *shared\ntail: keep\n",
			value:       []string{"new"},
			wantKind:    yaml.SequenceNode,
			wantTag:     "!!seq",
			wantContent: 1,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			root := doc.Content[0]
			originalValue := mappingValueForStringKey(t, root, "value")
			originalAlias := mappingValueForStringKey(t, root, "alias")
			require.Equal(t, yaml.AliasNode, originalAlias.Kind)
			require.Same(t, originalValue, originalAlias.Alias)
			originalKind := originalValue.Kind
			originalLineComment := originalValue.LineComment

			SetValue(root, "value", tt.value, SetValueOptions{SortKeys: true})

			liveValue := mappingValueForStringKey(t, root, "value")
			require.Same(t, originalValue, liveValue, "the anchor node identity must remain attached")
			require.Same(t, liveValue, originalAlias.Alias, "the external alias must follow the replacement")
			require.Equal(t, "shared", liveValue.Anchor)
			if originalKind == yaml.ScalarNode && tt.wantContent > 0 {
				require.Equal(t, originalLineComment, root.Content[0].LineComment)
				require.Empty(t, liveValue.LineComment)
			} else {
				require.Equal(t, originalLineComment, liveValue.LineComment)
			}
			require.Equal(t, tt.wantKind, liveValue.Kind)
			require.Equal(t, tt.wantTag, liveValue.Tag)
			require.Len(t, liveValue.Content, tt.wantContent)

			out, err := Marshal(doc)
			require.NoError(t, err)
			require.Contains(t, string(out), "# keep anchor comment")
			require.Contains(t, string(out), "*shared")
			require.NotContains(t, string(out), "!Widget")

			var round yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
			roundValue := mappingValueForStringKey(t, round.Content[0], "value")
			roundAlias := mappingValueForStringKey(t, round.Content[0], "alias")
			require.Equal(t, tt.wantKind, roundValue.Kind, "output:\n%s", out)
			require.Equal(t, tt.wantTag, roundValue.Tag, "output:\n%s", out)
			require.Equal(t, "shared", roundValue.Anchor, "output:\n%s", out)
			require.Equal(t, yaml.AliasNode, roundAlias.Kind, "output:\n%s", out)
			require.Same(t, roundValue, roundAlias.Alias, "output:\n%s", out)
		})
	}
}
