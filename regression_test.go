package yamledit

import (
	"bytes"
	"math"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestParseRejectsTrailingYAMLDocumentsAndContent(t *testing.T) {
	tests := []struct {
		name  string
		input string
	}{
		{
			name:  "second document",
			input: "first: value\n---\nsecond: value\n",
		},
		{
			name:  "empty second document",
			input: "first: value\n---\n",
		},
		{
			name:  "malformed second document",
			input: "first: value\n---\nbroken: [\n",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			_, err := Parse([]byte(tt.input))
			require.Error(t, err)
		})
	}
}

func TestValidateEditedOutputRejectsTrailingYAMLDocumentsAndContent(t *testing.T) {
	tests := []string{
		"first: value\n---\nsecond: value\n",
		"first: value\n---\nbroken: [\n",
	}

	for _, input := range tests {
		_, err := validateEditedOutput([]byte(input))
		require.Error(t, err, "input: %q", input)
	}
}

func TestSetScalarStringRoundTripsEscapedContent(t *testing.T) {
	tests := []struct {
		name  string
		input string
		value string
	}{
		{name: "backslashes in double quotes", input: "value: \"old\"\n", value: `C:\temp\new`},
		{name: "newline in single quotes", input: "value: 'old'\n", value: "first\nsecond"},
		{name: "control character", input: "value: old\n", value: "before\x00after"},
		{name: "next-line character", input: "value: old\n", value: "before\u0085after"},
		{name: "C1 control character", input: "value: old\n", value: "before\u0080after"},
		{name: "line-separator character", input: "value: old\n", value: "before\u2028after"},
		{name: "paragraph-separator character", input: "value: old\n", value: "before\u2029after"},
		{name: "embedded byte order mark", input: "value: old\n", value: "before\ufeffafter"},
		{name: "unicode noncharacter", input: "value: old\n", value: "before\uffffafter"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)

			SetScalarString(doc.Content[0], "value", tt.value)
			out, err := Marshal(doc)
			require.NoError(t, err)

			var got map[string]string
			require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
			require.Equal(t, tt.value, got["value"], "output:\n%s", out)
		})
	}
}

func TestSetScalarStringDoesNotChangeYAMLType(t *testing.T) {
	values := []string{"123", "1.5", "true", "TRUE", "null", ".nan", "2026-07-15"}
	for _, value := range values {
		t.Run(value, func(t *testing.T) {
			doc, err := Parse([]byte("value: old\n"))
			require.NoError(t, err)

			SetScalarString(doc.Content[0], "value", value)
			out, err := Marshal(doc)
			require.NoError(t, err)

			var round yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
			scalar := round.Content[0].Content[1]
			require.Equal(t, "!!str", scalar.Tag, "output:\n%s", out)
			require.Equal(t, value, scalar.Value)
		})
	}
}

func TestSetScalarFloatKeepsFloatType(t *testing.T) {
	tests := []struct {
		name  string
		value float64
	}{
		{name: "whole number", value: 1},
		{name: "negative zero", value: math.Copysign(0, -1)},
		{name: "not a number", value: math.NaN()},
		{name: "positive infinity", value: math.Inf(1)},
		{name: "negative infinity", value: math.Inf(-1)},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte("value: 0.5\n"))
			require.NoError(t, err)

			SetScalarFloat(doc.Content[0], "value", tt.value)
			out, err := Marshal(doc)
			require.NoError(t, err)

			var round yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
			scalar := round.Content[0].Content[1]
			require.Equal(t, "!!float", scalar.Tag, "output:\n%s", out)
			var got float64
			require.NoError(t, scalar.Decode(&got))
			switch {
			case math.IsNaN(tt.value):
				require.True(t, math.IsNaN(got))
			case math.IsInf(tt.value, 0):
				require.True(t, math.IsInf(got, int(math.Copysign(1, tt.value))))
			default:
				require.Equal(t, math.Float64bits(tt.value), math.Float64bits(got))
			}
		})
	}
}

func TestJSONPatchAppliesEveryScalarEditInSequenceItem(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - name: old\n    value: one\n    other: before\n"))
	require.NoError(t, err)

	patch := []byte(`[
		{"op":"replace","path":"/items/0/value","value":"two"},
		{"op":"replace","path":"/items/0/other","value":"after"}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)

	var got struct {
		Items []map[string]string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "old", got.Items[0]["name"])
	require.Equal(t, "two", got.Items[0]["value"])
	require.Equal(t, "after", got.Items[0]["other"])
}

func TestJSONPatchRemoveFieldInsideSequenceItem(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - keep: yes\n    remove: gone\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0/remove"}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []map[string]any `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	_, exists := got.Items[0]["remove"]
	require.False(t, exists, "output:\n%s", out)
}

func TestJSONPatchOnSequenceItemMappingHandleUsesAbsoluteOrderedPath(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - name: old\n    keep: true\n"))
	require.NoError(t, err)
	item := doc.Content[0].Content[1].Content[0]
	patch := []byte(`[
		{"op":"replace","path":"/name","value":"new"},
		{"op":"add","path":"/count","value":2},
		{"op":"remove","path":"/keep"}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(item, patch))

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []struct {
			Name  string `yaml:"name"`
			Count int    `yaml:"count"`
			Keep  *bool  `yaml:"keep"`
		} `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "new", got.Items[0].Name)
	require.Equal(t, 2, got.Items[0].Count)
	require.Nil(t, got.Items[0].Keep)
}

func TestJSONPatchRemoveKeepsASTMappingOrder(t *testing.T) {
	doc, err := Parse(nil)
	require.NoError(t, err)
	patch := []byte(`[
		{"op":"add","path":"/a","value":1},
		{"op":"add","path":"/b","value":2},
		{"op":"add","path":"/c","value":3},
		{"op":"remove","path":"/b"}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "a: 1\nc: 3\n", string(out))
}

func TestJSONPatchObjectReplacementRemovesOldMembers(t *testing.T) {
	for _, op := range []string{"add", "replace"} {
		t.Run(op, func(t *testing.T) {
			doc, err := Parse([]byte("obj:\n  keep: one\n  remove: two\n"))
			require.NoError(t, err)
			patch := []byte(`[{"op":"` + op + `","path":"/obj","value":{"keep":"updated","added":"three"}}]`)
			require.NoError(t, ApplyJSONPatchBytes(doc, patch))

			out, err := Marshal(doc)
			require.NoError(t, err)
			var got struct {
				Obj map[string]string `yaml:"obj"`
			}
			require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
			require.Equal(t, map[string]string{"added": "three", "keep": "updated"}, got.Obj)
		})
	}
}

func TestJSONPatchAddEmptyArrayKeepsSequenceType(t *testing.T) {
	doc, err := Parse([]byte("existing: true\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items","value":[]}]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	var round yaml.Node
	require.NoError(t, yaml.Unmarshal(out, &round), "output:\n%s", out)
	root := round.Content[0]
	for i := 0; i+1 < len(root.Content); i += 2 {
		if root.Content[i].Value == "items" {
			require.Equal(t, yaml.SequenceNode, root.Content[i+1].Kind, "output:\n%s", out)
			require.Empty(t, root.Content[i+1].Content)
			return
		}
	}
	t.Fatal("items key not found")
}

func TestJSONPatchTestComparesObjectsSemantically(t *testing.T) {
	doc, err := Parse([]byte("obj:\n  a: 1\n  nested:\n    ok: true\n"))
	require.NoError(t, err)
	patch := []byte(`[{"op":"test","path":"/obj","value":{"nested":{"ok":true},"a":1}}]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
}

func TestJSONPatchReplaceAndRemoveRequireExistingMember(t *testing.T) {
	for _, op := range []string{"replace", "remove"} {
		t.Run(op, func(t *testing.T) {
			doc, err := Parse([]byte("existing: true\n"))
			require.NoError(t, err)
			patch := `[{"op":"` + op + `","path":"/missing"`
			if op == "replace" {
				patch += `,"value":1`
			}
			patch += `}]`
			require.Error(t, ApplyJSONPatchBytes(doc, []byte(patch)))
		})
	}
}

func TestJSONPatchPointerHandlesObjectKeysAndEscapes(t *testing.T) {
	doc, err := Parse([]byte("\"\": empty\n\"0\": zero\n\"-\": dash\n\"a/b\": slash\n\"a~b\": tilde\n"))
	require.NoError(t, err)
	patch := []byte(`[
		{"op":"replace","path":"/","value":"EMPTY"},
		{"op":"replace","path":"/0","value":"ZERO"},
		{"op":"replace","path":"/-","value":"DASH"},
		{"op":"replace","path":"/a~1b","value":"SLASH"},
		{"op":"replace","path":"/a~0b","value":"TILDE"}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]string
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]string{"": "EMPTY", "0": "ZERO", "-": "DASH", "a/b": "SLASH", "a~b": "TILDE"}, got)
}

func TestJSONPatchPointerRejectsInvalidSyntax(t *testing.T) {
	tests := []string{
		`[{"op":"replace","path":"/a~2b","value":1}]`,
		`[{"op":"replace","path":"/items/01","value":1}]`,
	}
	for _, patch := range tests {
		doc, err := Parse([]byte("a~2b: 0\nitems:\n  - 0\n  - 1\n"))
		require.NoError(t, err)
		require.Error(t, ApplyJSONPatchBytes(doc, []byte(patch)))
	}
}

func TestJSONPatchEmptyPatchIsNoopAndTrailingJSONIsRejected(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[]`)))
	require.Error(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"test","path":"/a","value":1}] null`)))
}

func TestJSONPatchIgnoresExtensionMembersAndKeepsOpNamesCaseSensitive(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"test","path":"/a","value":1,"extension":true}]`)))
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/b","value":2,"from":123}]`)))
	require.Error(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"REPLACE","path":"/a","value":2}]`)))
}

func TestJSONPatchValidatesRequiredMembersAndIntermediateAppendToken(t *testing.T) {
	invalid := [][]byte{
		[]byte(`[{"op":"move","path":"/missing"}]`),
		[]byte(`[{"op":"move","from":"/missing"}]`),
		[]byte(`[{"op":"replace","path":"/a"}]`),
		[]byte(`[{"op":"test","path":null,"value":1}]`),
	}
	for _, patch := range invalid {
		doc, err := Parse([]byte("a: 1\nitems:\n  - x: old\n"))
		require.NoError(t, err)
		require.Error(t, ApplyJSONPatchBytes(doc, patch), "patch: %s", patch)
	}

	doc, err := Parse([]byte("items:\n  - x: old\n"))
	require.NoError(t, err)
	require.Error(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-/x","value":"new"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "items:\n  - x: old\n", string(out))
}

func TestJSONPatchSamePathMoveStillRequiresExistingSource(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	require.Error(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"move","from":"/missing","path":"/missing"}]`)))
}

func TestJSONPatchMovePrevalidatesShiftedIntermediateDestination(t *testing.T) {
	doc, err := Parse([]byte("arr:\n  - x: zero\n  - x: one\n  - x: two\n"))
	require.NoError(t, err)
	patch := []byte(`[{"op":"move","from":"/arr/0","path":"/arr/2/x"}]`)
	require.Error(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "arr:\n  - x: zero\n  - x: one\n  - x: two\n", string(out))
}

func TestJSONPatchMovePrevalidatesScalarDestinationParent(t *testing.T) {
	doc, err := Parse([]byte("a: scalar\nb: keep\n"))
	require.NoError(t, err)
	require.Error(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"move","from":"/b","path":"/a/x"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "a: scalar\nb: keep\n", string(out))
}

func TestJSONPatchPreservesExactJSONNumbersAndTestsByNumericValue(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	patch := []byte(`[
		{"op":"test","path":"/a","value":1.0},
		{"op":"add","path":"/precise","value":9007199254740993.0},
		{"op":"add","path":"/large","value":1e999},
		{"op":"test","path":"/precise","value":9007199254740993.0},
		{"op":"test","path":"/large","value":1e999}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "precise: 9007199254740993.0")
	require.Contains(t, string(out), "large: 1e999")
}

func TestJSONPatchCopyDereferencesOrdinaryAlias(t *testing.T) {
	doc, err := Parse([]byte("a: &shared\n  value: 1\nb: *shared\n"))
	require.NoError(t, err)
	patch := []byte(`[
		{"op":"test","path":"/b","value":{"value":1}},
		{"op":"copy","from":"/b","path":"/c"}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		C map[string]int `yaml:"c"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]int{"value": 1}, got.C)
}

func TestJSONPatchMoveUsesRemoveThenAddSemantics(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - a\n  - b\n  - c\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"move","from":"/items/0","path":"/items/2"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, []string{"b", "c", "a"}, got.Items)
}

func TestJSONPatchMoveSamePathIsNoop(t *testing.T) {
	doc, err := Parse([]byte("a: 1\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"move","from":"/a","path":"/a"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "a: 1\n", string(out))
}

func TestJSONPatchInvalidMoveDoesNotRemoveSource(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - a\n  - b\n"))
	require.NoError(t, err)
	err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"move","from":"/items/0","path":"/items/3"}]`))
	require.Error(t, err)
	out, marshalErr := Marshal(doc)
	require.NoError(t, marshalErr)
	var got struct {
		Items []string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, []string{"a", "b"}, got.Items)
}

func TestJSONPatchMoveAndCopyRespectBasePath(t *testing.T) {
	doc, err := Parse([]byte("root:\n  values:\n    a: 1\n    b: 2\n"))
	require.NoError(t, err)
	patch := []byte(`[
		{"op":"move","from":"/a","path":"/c"},
		{"op":"copy","from":"/b","path":"/d"}
	]`)
	require.NoError(t, ApplyJSONPatchAtPathBytes(doc, patch, []string{"root", "values"}))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Root struct {
			Values map[string]int `yaml:"values"`
		} `yaml:"root"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]int{"b": 2, "c": 1, "d": 2}, got.Root.Values)
}

func TestJSONPatchQuotesUnsafeNewMappingKeys(t *testing.T) {
	doc, err := Parse([]byte("existing: true\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/bad: key","value":"ok"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "ok", got["bad: key"])
}

func TestMappingHandleInsideSequenceCanEnsureSetAndDelete(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - nested:\n      keep: 1\n      remove: old\n"))
	require.NoError(t, err)
	item := doc.Content[0].Content[1].Content[0]
	require.Equal(t, yaml.MappingNode, item.Kind)

	nested := EnsurePath(item, "nested", "created")
	require.NotNil(t, nested)
	SetScalarInt(nested, "value", 2)
	originalNested := item.Content[1]
	DeleteKey(originalNested, "remove")

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []struct {
			Nested map[string]any `yaml:"nested"`
		} `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Len(t, got.Items, 1)
	require.EqualValues(t, 1, got.Items[0].Nested["keep"])
	_, removed := got.Items[0].Nested["remove"]
	require.False(t, removed, "output:\n%s", out)
	created, ok := got.Items[0].Nested["created"].(map[string]any)
	require.True(t, ok, "output:\n%s", out)
	require.EqualValues(t, 2, created["value"])
}

func TestSetNewScalarOnSequenceItem(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - name: one\n"))
	require.NoError(t, err)
	item := doc.Content[0].Content[1].Content[0]
	SetScalarString(item, "added", "value")

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []map[string]string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "one", got.Items[0]["name"])
	require.Equal(t, "value", got.Items[0]["added"])
}

func TestScalarSurgeryUsesUnicodeByteOffsets(t *testing.T) {
	tests := []struct {
		name  string
		input []byte
		key   string
	}{
		{name: "unicode key", input: []byte("键: old\n"), key: "键"},
		{name: "bom ascii key", input: append([]byte{0xef, 0xbb, 0xbf}, []byte("a: old\n")...), key: "a"},
		{name: "bom unicode key", input: append([]byte{0xef, 0xbb, 0xbf}, []byte("键: old\n")...), key: "键"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse(tt.input)
			require.NoError(t, err)
			SetScalarString(doc.Content[0], tt.key, "new")
			out, err := Marshal(doc)
			require.NoError(t, err)
			var got map[string]string
			require.NoError(t, yaml.Unmarshal(out, &got), "output: %q", out)
			require.Equal(t, "new", got[tt.key], "output: %q", out)
		})
	}
}

func TestScalarSurgeryPreservesAnchorAndAliases(t *testing.T) {
	doc, err := Parse([]byte("a: &x old\nb: *x\n"))
	require.NoError(t, err)
	SetScalarString(doc.Content[0], "a", "new")
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "a: &x new")
	var got map[string]string
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "new", got["a"])
	require.Equal(t, "new", got["b"])
}

func TestScalarTypeChangesRemoveIncompatibleExplicitTags(t *testing.T) {
	tests := []struct {
		name   string
		input  string
		update func(*yaml.Node)
		want   any
	}{
		{
			name:  "verbatim string tag containing comma to integer",
			input: "a: !<tag:yaml.org,2002:str> old\n",
			update: func(root *yaml.Node) {
				SetScalarInt(root, "a", 1)
			},
			want: 1,
		},
		{
			name:  "integer tag to string",
			input: "a: !!int 1\n",
			update: func(root *yaml.Node) {
				SetScalarString(root, "a", "new")
			},
			want: "new",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			tt.update(doc.Content[0])
			out, err := Marshal(doc)
			require.NoError(t, err)
			var got map[string]any
			require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
			require.Equal(t, tt.want, got["a"], "output:\n%s", out)
		})
	}
}

func TestScalarSurgerySkipsCompleteVerbatimTagBeforeEditingValue(t *testing.T) {
	doc, err := Parse([]byte("a: !<tag:yaml.org,2002:str> old\n"))
	require.NoError(t, err)
	SetScalarString(doc.Content[0], "a", "new")
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "!<tag:yaml.org,2002:str> new")
	var got map[string]string
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "new", got["a"])
}

func TestBlockScalarCanBecomeNonStringScalar(t *testing.T) {
	t.Run("mapping value", func(t *testing.T) {
		doc, err := Parse([]byte("x: |\n  old\nkeep: true\n"))
		require.NoError(t, err)
		SetScalarInt(doc.Content[0], "x", 1)
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]any
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, 1, got["x"])
		require.NotContains(t, string(out), "old")
	})

	t.Run("sequence item", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - |\n    old\n  - keep\n"))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/items/0","value":1}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []any `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, []any{1, "keep"}, got.Items)
		require.NotContains(t, string(out), "old")
	})
}

func TestScalarSurgeryPreservesCRLF(t *testing.T) {
	doc, err := Parse([]byte("a: old\r\nb: keep\r\n"))
	require.NoError(t, err)
	SetScalarString(doc.Content[0], "a", "new")
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.False(t, bytes.Contains(out, []byte("new\n")), "output: %q", out)
	require.Equal(t, "a: new\r\nb: keep\r\n", string(out))
}

func TestAnchoredImplicitNullRemainsValid(t *testing.T) {
	input := []byte("a: &x\nb: *x\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)
	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Nil(t, got["a"])
	require.Nil(t, got["b"])
}

func TestParserFallbackDoesNotRecurseForeverOnCyclicAlias(t *testing.T) {
	doc, err := Parse([]byte("a: 1\na: 2\nloop: &loop [*loop]\n"))
	require.NoError(t, err)
	require.NotNil(t, doc)
}

func TestDetachedMappingHandleCannotMutateLiveOrderedState(t *testing.T) {
	doc, err := Parse([]byte("obj:\n  old: value\n"))
	require.NoError(t, err)
	detached := doc.Content[0].Content[1]
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/obj","value":{"live":"yes"}}]`)))

	SetScalarString(detached, "stale", "no")
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Obj map[string]string `yaml:"obj"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]string{"live": "yes"}, got.Obj)
}

func TestFlowCollectionsAreNeverCorruptedBySurgery(t *testing.T) {
	t.Run("untouched duplicate flow map", func(t *testing.T) {
		input := []byte("obj: {a: 1, a: 2}\n")
		doc, err := Parse(input)
		require.NoError(t, err)
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, input, out)
	})

	tests := []struct {
		name  string
		input string
		patch string
	}{
		{name: "flow map", input: "obj: {a: old, b: keep}\n", patch: `[{"op":"replace","path":"/obj/a","value":"new"}]`},
		{name: "flow sequence", input: "items: [old, keep]\n", patch: `[{"op":"replace","path":"/items/0","value":"new"}]`},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(tt.patch)))
			out, marshalErr := Marshal(doc)
			if marshalErr != nil {
				return // unsupported is safer than returning corrupted YAML
			}
			var decoded any
			require.NoError(t, yaml.Unmarshal(out, &decoded), "output:\n%s", out)
		})
	}
}

func TestJSONPatchAppendPreservesNestedSequenceItemTypes(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - name: existing\n    meta:\n      x: old\n"))
	require.NoError(t, err)
	patch := []byte(`[{"op":"add","path":"/items/-","value":{"name":"new","meta":{"x":"new"},"tags":["123","true"]}}]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)

	var got struct {
		Items []struct {
			Name string            `yaml:"name"`
			Meta map[string]string `yaml:"meta"`
			Tags []string          `yaml:"tags"`
		} `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Len(t, got.Items, 2)
	require.Equal(t, "new", got.Items[1].Name)
	require.Equal(t, map[string]string{"x": "new"}, got.Items[1].Meta)
	require.Equal(t, []string{"123", "true"}, got.Items[1].Tags)
}

func TestJSONPatchNewSequencePreservesNestedTypesAndQuotesKeys(t *testing.T) {
	doc, err := Parse([]byte("existing: true\n"))
	require.NoError(t, err)
	patch := []byte(`[{"op":"add","path":"/items","value":[{
		"meta":{"unsafe:key":"value"},
		"nested":[{"x":"y"}]
	}]}]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []struct {
			Meta   map[string]string   `yaml:"meta"`
			Nested []map[string]string `yaml:"nested"`
		} `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "value", got.Items[0].Meta["unsafe:key"])
	require.Equal(t, "y", got.Items[0].Nested[0]["x"])
}

func TestJSONPatchNestedArraysRenderRecursively(t *testing.T) {
	t.Run("new sequence", func(t *testing.T) {
		doc, err := Parse([]byte("existing: true\n"))
		require.NoError(t, err)
		patch := []byte(`[{"op":"add","path":"/matrix","value":[[{"x":"y"}]]}]`)
		require.NoError(t, ApplyJSONPatchBytes(doc, patch))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Matrix [][]map[string]string `yaml:"matrix"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, "y", got.Matrix[0][0]["x"])
	})

	t.Run("append to existing sequence", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - existing\n"))
		require.NoError(t, err)
		patch := []byte(`[{"op":"add","path":"/items/-","value":[{"x":"y"}]}]`)
		require.NoError(t, ApplyJSONPatchBytes(doc, patch))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []any `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		nested, ok := got.Items[1].([]any)
		require.True(t, ok, "output:\n%s", out)
		require.Equal(t, map[string]any{"x": "y"}, nested[0])
	})
}

func TestDuplicateSequenceAppendUsesWinningOccurrence(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - a\nitems:\n  - a\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":"b"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, 1, bytes.Count(out, []byte("items:")), "output:\n%s", out)
	var got struct {
		Items []string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, []string{"a", "b"}, got.Items)
}

func TestDuplicateCleanupKeepsWinningScalarValue(t *testing.T) {
	doc, err := Parse([]byte("a: first\na: last\n"))
	require.NoError(t, err)
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "a: last\n", string(out))
}

func TestUnsafeCompactSequenceDuplicateIsPreservedRatherThanCorrupted(t *testing.T) {
	input := []byte("items:\n  - dup: first\n    dup: last\n    keep: yes\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)
}

func TestDuplicateParentBlockScalarUsesWinningOccurrence(t *testing.T) {
	doc, err := Parse([]byte("a:\n  x: target\na:\n  x: |\n    old\n"))
	require.NoError(t, err)
	winning := EnsurePath(doc, "a")
	SetScalarString(winning, "x", "target")
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, 1, bytes.Count(out, []byte("a:")), "output:\n%s", out)
	var got struct {
		A map[string]string `yaml:"a"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "target", got.A["x"])
}

func TestMarshalPropagatesEncoderErrors(t *testing.T) {
	_, err := Marshal(&yaml.Node{Kind: yaml.Kind(99)})
	require.Error(t, err)
}

func TestConcurrentJSONPatchArrayAppends(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - seed\n"))
	require.NoError(t, err)

	const workers = 16
	var wg sync.WaitGroup
	errs := make(chan error, workers)
	for i := 0; i < workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			errs <- ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":"item"}]`))
		}()
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		require.NoError(t, err)
	}

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Len(t, got.Items, workers+1)
}

func TestConcurrentMarshalOfInitiallyEmptyDocument(t *testing.T) {
	doc, err := Parse(nil)
	require.NoError(t, err)
	root := doc.Content[0]

	var wg sync.WaitGroup
	marshalErrs := make(chan error, 50)
	for i := 0; i < 50; i++ {
		wg.Add(2)
		go func(value int) {
			defer wg.Done()
			SetScalarInt(root, "value", value)
		}(i)
		go func() {
			defer wg.Done()
			_, marshalErr := Marshal(doc)
			marshalErrs <- marshalErr
		}()
	}
	wg.Wait()
	close(marshalErrs)
	for marshalErr := range marshalErrs {
		require.NoError(t, marshalErr)
	}
}

func TestStructuralRewriteKeepsSequenceItemDash(t *testing.T) {
	doc, err := Parse([]byte("empty:\nlist:\n  - name: old\n    keep: value\n"))
	require.NoError(t, err)
	item := doc.Content[0].Content[3].Content[0]
	SetScalarString(item, "name", "new")

	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		List []map[string]string `yaml:"list"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Len(t, got.List, 1)
	require.Equal(t, "new", got.List[0]["name"])
	require.Equal(t, "value", got.List[0]["keep"])
}

func TestDeletingLastMappingMemberKeepsEmptyMapType(t *testing.T) {
	t.Run("document root", func(t *testing.T) {
		doc, err := Parse([]byte("# header\nonly: value\n# footer\n"))
		require.NoError(t, err)
		DeleteKey(doc.Content[0], "only")
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Contains(t, string(out), "# header\n{}\n# footer")
		var got map[string]any
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Empty(t, got)
	})

	t.Run("mapping sequence item", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - only: value\n"))
		require.NoError(t, err)
		item := doc.Content[0].Content[1].Content[0]
		DeleteKey(item, "only")
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []map[string]any `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Len(t, got.Items, 1)
		require.Empty(t, got.Items[0])
	})

	t.Run("add to empty mapping sequence item", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - {}\n"))
		require.NoError(t, err)
		item := doc.Content[0].Content[1].Content[0]
		SetScalarString(item, "added", "value")
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []map[string]string `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, map[string]string{"added": "value"}, got.Items[0])
	})
}

func TestStructuralRewriteTreatsBracketShapedObjectKeyAsKey(t *testing.T) {
	doc, err := Parse([]byte("outer:\n  \"[0]\":\n    old: x\n"))
	require.NoError(t, err)
	patch := []byte(`[{"op":"replace","path":"/outer/[0]","value":{"new":"y"}}]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Outer map[string]map[string]string `yaml:"outer"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]string{"new": "y"}, got.Outer["[0]"])
}

func TestExplicitCollectionKeysFailSafelyInsteadOfLeavingOrphanValue(t *testing.T) {
	inputs := []string{
		"? explicit\n:\n  nested: old\n",
		"? explicit\n:\n  - old\n",
	}
	for _, input := range inputs {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		DeleteKey(doc.Content[0], "explicit")
		_, err = Marshal(doc)
		require.Error(t, err)
	}
}

func TestSequenceFirstFieldDeletionPreservesItemDash(t *testing.T) {
	tests := []string{
		"items:\n  - remove: gone\n    keep: yes\n",
		"items:\n  - ? remove\n    : gone\n    keep: yes\n",
	}
	for _, input := range tests {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0/remove"}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []map[string]any `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, []map[string]any{{"keep": "yes"}}, got.Items)
	}
}

func TestCompactExplicitSequenceItemCanBeRewrittenSafely(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - ? explicit\n    : old\n"))
	require.NoError(t, err)
	item := doc.Content[0].Content[1].Content[0]
	SetScalarString(item, "new", "x")
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []map[string]string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]string{"explicit": "old", "new": "x"}, got.Items[0])
}

func TestUnsupportedExplicitOccurrenceCannotBeMaskedBySafeOccurrence(t *testing.T) {
	doc, err := Parse([]byte("a: normal\n? a\n: explicit\nkeep: yes\n"))
	require.NoError(t, err)
	DeleteKey(doc.Content[0], "a")
	_, err = Marshal(doc)
	require.Error(t, err)
}

func TestBOMIsPreservedAndDoesNotHideExplicitKey(t *testing.T) {
	t.Run("ordinary key edit", func(t *testing.T) {
		input := []byte("\ufeffa: old\n")
		doc, err := Parse(input)
		require.NoError(t, err)
		SetScalarString(doc.Content[0], "a", "new")
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.True(t, bytes.HasPrefix(out, []byte{0xef, 0xbb, 0xbf}), "output bytes: %v", out)
	})

	t.Run("explicit key deletion", func(t *testing.T) {
		doc, err := Parse([]byte("\ufeff? explicit\n: old\n"))
		require.NoError(t, err)
		DeleteKey(doc.Content[0], "explicit")
		_, err = Marshal(doc)
		require.Error(t, err)
	})
}

func TestStructuralRewriteDoesNotTreatQuotedHashAsComment(t *testing.T) {
	doc, err := Parse([]byte("empty:\nx: \"old#secret\"\n"))
	require.NoError(t, err)
	patch := []byte(`[{"op":"replace","path":"/x","value":{"nested":"new"}}]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.NotContains(t, string(out), "old#secret")
	require.NotContains(t, string(out), "#secret")
	var got struct {
		X map[string]string `yaml:"x"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]string{"nested": "new"}, got.X)
}

func TestBlockScalarReplacementPreservesTrailingNewlines(t *testing.T) {
	doc, err := Parse([]byte("x: |\n  old\n"))
	require.NoError(t, err)
	want := "a\n\n"
	SetScalarString(doc.Content[0], "x", want)
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]string
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, want, got["x"], "output:\n%s", out)
}

func TestSequenceAppendDoesNotSplitTrailingBlockScalar(t *testing.T) {
	t.Run("scalar item", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - |\n    hello\n"))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":"new"}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []string `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, []string{"hello\n", "new"}, got.Items)
	})

	t.Run("mapping item", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - name: one\n    script: |\n      echo hello\n"))
		require.NoError(t, err)
		patch := []byte(`[{"op":"add","path":"/items/-","value":{"name":"two","script":"echo two\n"}}]`)
		require.NoError(t, ApplyJSONPatchBytes(doc, patch))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []map[string]string `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Len(t, got.Items, 2)
		require.Equal(t, "echo hello\n", got.Items[0]["script"])
		require.Equal(t, "echo two\n", got.Items[1]["script"])
	})
}

func TestDeleteKeyPreservesFollowingAndFooterComments(t *testing.T) {
	input := []byte("a: 1\n# docs for b\nb: 2\n# footer\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	DeleteKey(doc.Content[0], "a")
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "# docs for b\nb: 2\n# footer\n", string(out))
}

func TestInternalPathEncodingDoesNotCollideWithYAMLKeys(t *testing.T) {
	input := []byte("\"a\\0p\\0b\": root\na:\n  b: nested\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	specialKey := "a\x00p\x00b"
	SetScalarString(doc.Content[0], specialKey, "changed")
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got), "output: %q", out)
	require.Equal(t, "changed", got[specialKey])
	nested, ok := got["a"].(map[string]any)
	require.True(t, ok, "output: %q", out)
	require.Equal(t, "nested", nested["b"])
}

func TestIndentDetectionIgnoresBlockScalarContent(t *testing.T) {
	doc, err := Parse([]byte("root:\n    text: |\n      hello\n    existing: true\n"))
	require.NoError(t, err)
	created := EnsurePath(doc, "root", "created")
	SetScalarInt(created, "value", 1)
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "    created:\n        value: 1", "output:\n%s", out)
}

func TestEnsurePathUsesLastDuplicateMapping(t *testing.T) {
	doc, err := Parse([]byte("a:\n  x: 1\na:\n  x: 2\n"))
	require.NoError(t, err)
	a := EnsurePath(doc, "a")
	SetScalarInt(a, "z", 3)
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]map[string]int
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]int{"x": 2, "z": 3}, got["a"])
	require.Equal(t, 1, bytes.Count(out, []byte("a:\n")), "output:\n%s", out)
}

func TestMultilineScalarsUseWholeEntryRewrite(t *testing.T) {
	tests := []string{
		"value: \"old\n  continuation\"\nkeep: yes\n",
		"value: 'old\n  continuation'\nkeep: yes\n",
		"value: old\n  continuation\nkeep: yes\n",
	}
	for _, input := range tests {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		SetScalarString(doc.Content[0], "value", "new")
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]string
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, "new", got["value"], "output:\n%s", out)
		require.Equal(t, "yes", got["keep"], "output:\n%s", out)
		require.NotContains(t, string(out), "continuation")
	}
}

func TestFallbackAliasExpansionHasResourceLimit(t *testing.T) {
	var source bytes.Buffer
	source.WriteString("a: &a [x, x, x, x, x, x, x, x, x, x]\n")
	for name := byte('b'); name <= byte('h'); name++ {
		source.WriteByte(name)
		source.WriteString(": &")
		source.WriteByte(name)
		source.WriteString(" [")
		for i := 0; i < 10; i++ {
			if i > 0 {
				source.WriteString(", ")
			}
			source.WriteString("*")
			source.WriteByte(name - 1)
		}
		source.WriteString("]\n")
	}
	// Force the goccy ordered-map decoder onto the yaml.v3 fallback path.
	source.WriteString("duplicate: first\nduplicate: last\n")

	_, err := Parse(source.Bytes())
	require.ErrorContains(t, err, "alias expansion limit")
}

func TestStandaloneSequenceDashIsIncludedInShapeRewrite(t *testing.T) {
	doc, err := Parse([]byte("items:\n  -\n    k: old\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":{"k":"new"}}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []map[string]string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, []map[string]string{{"k": "old"}, {"k": "new"}}, got.Items)
}

func TestTypedAndStringScalarKeysAreNotCollapsed(t *testing.T) {
	input := []byte("1: integer\n\"1\": string\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)
}

func TestExplicitEmptyMappingsCanBeEditedOrReturnToOriginal(t *testing.T) {
	t.Run("add root member", func(t *testing.T) {
		doc, err := Parse([]byte("{}\n"))
		require.NoError(t, err)
		SetScalarString(doc.Content[0], "added", "value")
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]string
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, map[string]string{"added": "value"}, got)
	})

	t.Run("net zero root edit", func(t *testing.T) {
		input := []byte("{}\n")
		doc, err := Parse(input)
		require.NoError(t, err)
		SetScalarString(doc.Content[0], "temporary", "value")
		DeleteKey(doc.Content[0], "temporary")
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, input, out)
	})

	t.Run("document wrapper is preserved", func(t *testing.T) {
		inputs := [][]byte{
			[]byte("\ufeff---\n{}\n...\n"),
			[]byte("%YAML 1.1\n---\n{}\n...\n"),
		}
		for _, input := range inputs {
			doc, err := Parse(input)
			require.NoError(t, err)
			SetScalarString(doc.Content[0], "added", "value")
			out, err := Marshal(doc)
			require.NoError(t, err)
			if bytes.HasPrefix(input, []byte{0xef, 0xbb, 0xbf}) {
				require.True(t, bytes.HasPrefix(out, []byte{0xef, 0xbb, 0xbf}), "output: %q", out)
			}
			require.Contains(t, string(out), "---\n")
			require.Contains(t, string(out), "\n...\n")
			if bytes.HasPrefix(input, []byte("%YAML")) {
				require.Contains(t, string(out), "%YAML 1.1")
			}
		}
	})

	t.Run("net zero sequence item edit", func(t *testing.T) {
		input := []byte("items:\n  - {}\n")
		doc, err := Parse(input)
		require.NoError(t, err)
		item := doc.Content[0].Content[1].Content[0]
		SetScalarString(item, "temporary", "value")
		DeleteKey(item, "temporary")
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, input, out)
	})
}

func TestAnchorSafetyAcrossStructuralChanges(t *testing.T) {
	t.Run("anchored block scalar keeps definition", func(t *testing.T) {
		doc, err := Parse([]byte("value: &shared |\n  old\ncopy: *shared\n"))
		require.NoError(t, err)
		SetScalarInt(doc.Content[0], "value", 7)
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Contains(t, string(out), "&shared")
		var got map[string]any
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, 7, got["value"])
		require.Equal(t, 7, got["copy"])
	})

	t.Run("removing a referenced anchor fails", func(t *testing.T) {
		doc, err := Parse([]byte("value: &shared old\ncopy: *shared\n"))
		require.NoError(t, err)
		DeleteKey(doc.Content[0], "value")
		_, err = Marshal(doc)
		require.ErrorContains(t, err, "invalid YAML")
	})

	t.Run("sequence item metadata blocks lossy shape rewrite", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - &shared\n    value: old\ncopy: *shared\n"))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":{"value":"new"}}]`)))
		_, err = Marshal(doc)
		require.Error(t, err)
	})
}

func TestCollectionTagSurvivesStructuralRewrite(t *testing.T) {
	tests := []struct {
		input string
		tag   string
	}{
		{input: "items: !Widget [old] # retain\n", tag: "!Widget"},
		{input: "items: !<tag:example.com,2026:Widget> [old]\n", tag: "tag:example.com,2026:Widget"},
	}
	for _, tt := range tests {
		doc, err := Parse([]byte(tt.input))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/items/0","value":"new"}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var parsed yaml.Node
		require.NoError(t, yaml.Unmarshal(out, &parsed), "output:\n%s", out)
		require.Equal(t, tt.tag, parsed.Content[0].Content[1].Tag, "output:\n%s", out)
		if bytes.Contains([]byte(tt.input), []byte("# retain")) {
			require.Contains(t, string(out), "# retain")
		}
	}
}

func TestInvalidUTF8EditFailsInsteadOfChangingStringMeaning(t *testing.T) {
	doc, err := Parse([]byte("value: old\n"))
	require.NoError(t, err)
	SetScalarString(doc.Content[0], "value", string([]byte{0xff}))
	_, err = Marshal(doc)
	require.ErrorContains(t, err, "invalid UTF-8")
}

func TestJSONPatchAddDoesNotCreateMissingParentsOnFailure(t *testing.T) {
	input := []byte("existing: value\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/missing/child","value":1}]`))
	require.Error(t, err)
	out, marshalErr := Marshal(doc)
	require.NoError(t, marshalErr)
	require.Equal(t, input, out)
}

func TestJSONPatchFailureIsAtomic(t *testing.T) {
	input := []byte("value: old\nkeep: yes\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	err = ApplyJSONPatchBytes(doc, []byte(`[
		{"op":"replace","path":"/value","value":"new"},
		{"op":"remove","path":"/missing"}
	]`))
	require.Error(t, err)
	out, marshalErr := Marshal(doc)
	require.NoError(t, marshalErr)
	require.Equal(t, input, out)
}

func TestJSONPatchCannotCopyNonJSONMappingKeys(t *testing.T) {
	input := []byte("source:\n  1: integer-key\nkeep: yes\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"copy","from":"/source","path":"/copy"}]`))
	require.ErrorContains(t, err, "not JSON-compatible")
	out, marshalErr := Marshal(doc)
	require.NoError(t, marshalErr)
	require.Equal(t, input, out)
}

func TestJSONPatchCannotCopyYAMLOnlyScalarTypes(t *testing.T) {
	for _, input := range []string{"source: !Widget value\n", "source: 2026-07-15\n"} {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"copy","from":"/source","path":"/copy"}]`))
		require.ErrorContains(t, err, "not JSON-compatible")
		out, marshalErr := Marshal(doc)
		require.NoError(t, marshalErr)
		require.Equal(t, []byte(input), out)
	}
}

func TestJSONPatchTestUnderstandsYAMLNumericSyntax(t *testing.T) {
	input := []byte("hex: 0x10\nunderscored: 1_000\nfraction: 1_000.5\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	patch := []byte(`[
		{"op":"test","path":"/hex","value":16},
		{"op":"test","path":"/underscored","value":1000},
		{"op":"test","path":"/fraction","value":1000.5}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)
}

func TestJSONPatchRejectsInvalidUTF8BeforeJSONDecoding(t *testing.T) {
	doc, err := Parse([]byte("value: old\n"))
	require.NoError(t, err)
	patch := append([]byte(`[{"op":"replace","path":"/value","value":"`), 0xff)
	patch = append(patch, []byte(`"}]`)...)
	err = ApplyJSONPatchBytes(doc, patch)
	require.ErrorContains(t, err, "not valid UTF-8")
	out, marshalErr := Marshal(doc)
	require.NoError(t, marshalErr)
	require.Equal(t, []byte("value: old\n"), out)
}

func TestInsertedSequenceMappingSupportsOneSpaceIndent(t *testing.T) {
	doc, err := Parse([]byte("root:\n a: b\n"))
	require.NoError(t, err)
	patch := []byte(`[{"op":"add","path":"/root/items","value":[{"x":1,"y":2}]}]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Root struct {
			Items []map[string]int `yaml:"items"`
		} `yaml:"root"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, []map[string]int{{"x": 1, "y": 2}}, got.Root.Items)
}

func TestUnsafePromotionDoesNotDropUntouchedMetadata(t *testing.T) {
	inputs := []string{
		"items:\n  - remove: gone\n    tagged: !foo value\n",
		"items:\n  - remove: gone\n    anchored: &local value\n",
	}
	for _, input := range inputs {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0/remove"}]`)))
		_, err = Marshal(doc)
		require.Error(t, err, "input:\n%s", input)
	}

	t.Run("typed key in rewritten item", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - 1: integer\n"))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/0/new","value":"x"}]`)))
		_, err = Marshal(doc)
		require.Error(t, err)
	})

	t.Run("untouched comment and block style", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - remove: gone\n    keep: | # retain\n      hello\n"))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0/remove"}]`)))
		_, err = Marshal(doc)
		require.Error(t, err)
	})
}

func TestFlowMetadataBlocksLossyAncestorRewrite(t *testing.T) {
	tests := []struct {
		name  string
		input string
	}{
		{
			name:  "custom tag",
			input: "outer: {remove: gone, tagged: !foo value}\n",
		},
		{
			name:  "alias",
			input: "base: &shared {value: old}\nouter: {remove: gone, ref: *shared}\n",
		},
		{
			name:  "typed key",
			input: "outer: {1: integer, remove: gone}\n",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/outer/remove"}]`)))
			_, err = Marshal(doc)
			require.Error(t, err)
		})
	}
}

func TestAliasBlocksLossySequencePromotion(t *testing.T) {
	doc, err := Parse([]byte("base: &shared {value: old}\nitems:\n  - remove: gone\n    keep: yes\n  - *shared\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/0/remove"}]`)))
	_, err = Marshal(doc)
	require.Error(t, err)
}

func TestMultilineExplicitKeyDeletionFailsSafely(t *testing.T) {
	input := []byte("?\n  explicit\n: old\nkeep: yes\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	DeleteKey(doc.Content[0], "explicit")
	_, err = Marshal(doc)
	require.Error(t, err)
}

func TestWinningDuplicateParentReceivesChildEdit(t *testing.T) {
	doc, err := Parse([]byte("a:\n  shadow: old\na:\n  keep: yes\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/a/shadow","value":"new"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]map[string]string
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, map[string]string{"keep": "yes", "shadow": "new"}, got["a"])
	require.Equal(t, 1, bytes.Count(out, []byte("a:\n")), "output:\n%s", out)
}

func TestComplexAnchorReplacementKeepsAliasPointersConsistent(t *testing.T) {
	input := []byte("a: &shared {old: 1}\nb: *shared\n")

	t.Run("later test sees replacement", func(t *testing.T) {
		doc, err := Parse(input)
		require.NoError(t, err)
		patch := []byte(`[
			{"op":"replace","path":"/a","value":{"new":2}},
			{"op":"test","path":"/b","value":{"old":1}}
		]`)
		require.Error(t, ApplyJSONPatchBytes(doc, patch))
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, input, out)
	})

	t.Run("serialized alias resolves to replacement", func(t *testing.T) {
		doc, err := Parse(input)
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/a","value":{"new":2}}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]map[string]int
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, map[string]int{"new": 2}, got["a"])
		require.Equal(t, map[string]int{"new": 2}, got["b"])
	})
}

func TestMoveRejectsYAMLMetadataAtomically(t *testing.T) {
	tests := []string{
		"src: !Widget\n  x: 1\nkeep: yes\n",
		"src: &unused\n  x: 1\nkeep: yes\n",
		"src: 'styled' # retain\nkeep: yes\n",
		"src: 2026-07-15\nkeep: yes\n",
	}
	for _, input := range tests {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"move","from":"/src","path":"/dest"}]`))
		require.ErrorContains(t, err, "metadata", "input:\n%s", input)
		out, marshalErr := Marshal(doc)
		require.NoError(t, marshalErr)
		require.Equal(t, []byte(input), out)
	}
}

func TestRemovingReusedAnchorDoesNotRetargetAlias(t *testing.T) {
	input := []byte("old: &same one\nnew: &same two\nref: *same\n")

	t.Run("JSON Patch rejects removal atomically", func(t *testing.T) {
		doc, err := Parse(input)
		require.NoError(t, err)
		err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/new"}]`))
		require.ErrorContains(t, err, "still referenced")
		out, marshalErr := Marshal(doc)
		require.NoError(t, marshalErr)
		require.Equal(t, input, out)
	})

	t.Run("setter marshal detects exact removed target", func(t *testing.T) {
		doc, err := Parse(input)
		require.NoError(t, err)
		DeleteKey(doc.Content[0], "new")
		_, err = Marshal(doc)
		require.ErrorContains(t, err, "invalid YAML alias")
	})
}

func TestExplicitEmptyRootKeepsTagOrAnchorBinding(t *testing.T) {
	tests := []struct {
		name   string
		input  string
		tag    string
		anchor string
	}{
		{name: "custom tag", input: "!Widget {}\n", tag: "!Widget"},
		{name: "anchor", input: "&root {}\n", tag: "!!map", anchor: "root"},
		{name: "tag after document marker", input: "--- !Widget {}\n...\n", tag: "!Widget"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/x","value":1}]`)))
			out, err := Marshal(doc)
			require.NoError(t, err)

			var reparsed yaml.Node
			require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
			root := reparsed.Content[0]
			require.Equal(t, tt.tag, root.Tag, "output:\n%s", out)
			require.Equal(t, tt.anchor, root.Anchor, "output:\n%s", out)
			require.Len(t, root.Content, 2, "output:\n%s", out)
			require.Equal(t, "x", root.Content[0].Value, "output:\n%s", out)
		})
	}
}

func TestNonStringYAMLKeyCollisionsFailWithoutMutation(t *testing.T) {
	input := []byte("1: integer\n\"1\": string\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/1"}]`))
	require.ErrorContains(t, err, "non-string YAML key")
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)

	doc, err = Parse([]byte("\"1\": {string: old}\n1: {numeric: old}\n"))
	require.NoError(t, err)
	require.Nil(t, EnsurePath(doc, "1"))
	SetScalarString(doc.Content[0], "1", "changed")
	out, err = Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, []byte("\"1\": {string: old}\n1: {numeric: old}\n"), out)
}

func TestRemovingAnchoredMappingKeyChecksAliasIdentity(t *testing.T) {
	input := []byte("&same old: one\n&same new: two\nref: *same\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/new"}]`))
	require.ErrorContains(t, err, "still referenced")
	out, marshalErr := Marshal(doc)
	require.NoError(t, marshalErr)
	require.Equal(t, input, out)
}

func TestJSONPatchClearsOrRebasesPriorDeletionMarkers(t *testing.T) {
	t.Run("re-add same member", func(t *testing.T) {
		doc, err := Parse([]byte("a: old\nkeep: yes\n"))
		require.NoError(t, err)
		DeleteKey(doc.Content[0], "a")
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/a","value":"new"}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]any
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, "new", got["a"])
	})

	t.Run("replace parent clears descendant marker", func(t *testing.T) {
		doc, err := Parse([]byte("a:\n  b: old\n  keep: yes\n"))
		require.NoError(t, err)
		DeleteKey(doc.Content[0].Content[1], "b")
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/a","value":{"new":1}}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]map[string]int
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, map[string]int{"new": 1}, got["a"])
	})

	t.Run("append keeps existing item deletion", func(t *testing.T) {
		doc, err := Parse([]byte("items:\n  - a: old\n  - b: keep\n"))
		require.NoError(t, err)
		items := doc.Content[0].Content[1]
		DeleteKey(items.Content[0], "a")
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":{"c":"new"}}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got struct {
			Items []map[string]string `yaml:"items"`
		}
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.NotContains(t, got.Items[0], "a")
		require.Equal(t, "new", got.Items[2]["c"])
	})
}

func TestMoveRejectsMetadataOnSourceKey(t *testing.T) {
	input := []byte("# important\nsrc: 1\nkeep: yes\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	err = ApplyJSONPatchBytes(doc, []byte(`[{"op":"move","from":"/src","path":"/dest"}]`))
	require.ErrorContains(t, err, "metadata")
	out, marshalErr := Marshal(doc)
	require.NoError(t, marshalErr)
	require.Equal(t, input, out)
}

func TestMoveSupportsEmptyJSONContainers(t *testing.T) {
	doc, err := Parse([]byte("empty: []\nobj:\n  nested: {}\n"))
	require.NoError(t, err)
	patch := []byte(`[
		{"op":"move","from":"/empty","path":"/moved"},
		{"op":"move","from":"/obj","path":"/movedObj"}
	]`)
	require.NoError(t, ApplyJSONPatchBytes(doc, patch))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, []any{}, got["moved"])
	require.Equal(t, map[string]any{"nested": map[string]any{}}, got["movedObj"])

	t.Run("append then move", func(t *testing.T) {
		doc, err := Parse([]byte("source: []\nkeep: yes\n"))
		require.NoError(t, err)
		patch := []byte(`[
			{"op":"add","path":"/source/-","value":1},
			{"op":"move","from":"/source","path":"/moved"}
		]`)
		require.NoError(t, ApplyJSONPatchBytes(doc, patch))
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]any
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, []any{1}, got["moved"])
	})
}

func TestParseRejectsLoneCarriageReturnLineEndings(t *testing.T) {
	_, err := Parse([]byte("a: 1\rb: 2\r"))
	require.ErrorContains(t, err, "carriage-return")
	doc, err := Parse([]byte("a: 1\r\nb: 2\r\n"))
	require.NoError(t, err)
	require.NotNil(t, doc)
}

func TestShadowedDuplicateMappingHandlesCannotChangeWinner(t *testing.T) {
	input := []byte("dup:\n  x: first\ndup:\n  x: second\n")

	t.Run("setter", func(t *testing.T) {
		doc, err := Parse(input)
		require.NoError(t, err)
		shadowed := doc.Content[0].Content[1]
		SetScalarString(shadowed, "x", "changed")
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]map[string]string
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, "second", got["dup"]["x"])
	})

	t.Run("JSON Patch", func(t *testing.T) {
		doc, err := Parse(input)
		require.NoError(t, err)
		shadowed := doc.Content[0].Content[1]
		err = ApplyJSONPatchBytes(shadowed, []byte(`[{"op":"replace","path":"/x","value":"changed"}]`))
		require.Error(t, err)
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]map[string]string
		require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
		require.Equal(t, "second", got["dup"]["x"])
	})
}

func TestSequenceShapeRewriteDoesNotDropYAMLMetadata(t *testing.T) {
	inputs := []string{
		"items:\n  - tagged: !foo value\n    keep: yes\n  - remove: me\n",
		"items:\n  - date: 2026-07-15\n    keep: yes\n  - remove: me\n",
		"base: &base original\nitems:\n  - ref: *base\n    keep: yes\n  - remove: me\n",
	}
	for _, input := range inputs {
		doc, err := Parse([]byte(input))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/1"}]`)))
		_, err = Marshal(doc)
		require.Error(t, err, "input:\n%s", input)
	}
}

func TestMixedSequenceScalarCommentIsNotSilentlyDropped(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - one # preserve me\n  - name: two\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"replace","path":"/items/0","value":"ONE"}]`)))
	out, err := Marshal(doc)
	if err == nil {
		require.Contains(t, string(out), "# preserve me", "output:\n%s", out)
	}
}

func TestNoopNaNPreservesExactBytes(t *testing.T) {
	input := []byte("a: .NaN # exact\nkeep: yes\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, out)
}

func TestExplicitYAMLBoolUsesDecodedValueForJSONPatch(t *testing.T) {
	doc, err := Parse([]byte("a: !!bool yes\n"))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"test","path":"/a","value":true}]`)))
}

func TestTriviaOnlyDocumentsRemainEditable(t *testing.T) {
	inputs := [][]byte{
		[]byte("\n"),
		[]byte("# header only\n"),
		{0xef, 0xbb, 0xbf},
	}
	for _, input := range inputs {
		doc, err := Parse(input)
		require.NoError(t, err, "input: %q", input)
		unchanged, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, input, unchanged)

		SetScalarString(doc.Content[0], "x", "value")
		out, err := Marshal(doc)
		require.NoError(t, err)
		var got map[string]string
		require.NoError(t, yaml.Unmarshal(out, &got), "output: %q", out)
		require.Equal(t, "value", got["x"])
		if bytes.HasPrefix(input, []byte{0xef, 0xbb, 0xbf}) {
			require.True(t, bytes.HasPrefix(out, []byte{0xef, 0xbb, 0xbf}))
		}
		if bytes.Contains(input, []byte("# header only")) {
			require.Contains(t, string(out), "# header only")
		}
	}
}

func TestGeneratedPatchesUseOriginalCRLFStyle(t *testing.T) {
	t.Run("mapping insertion", func(t *testing.T) {
		doc, err := Parse([]byte("a: 1\r\nkeep: yes\r\n"))
		require.NoError(t, err)
		SetScalarInt(doc.Content[0], "b", 2)
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, "a: 1\r\nkeep: yes\r\nb: 2\r\n", string(out))
	})

	t.Run("sequence append", func(t *testing.T) {
		doc, err := Parse([]byte("items:\r\n  - one\r\n"))
		require.NoError(t, err)
		require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/-","value":"two"}]`)))
		out, err := Marshal(doc)
		require.NoError(t, err)
		for i, b := range out {
			if b == '\n' {
				require.Greater(t, i, 0)
				require.Equal(t, byte('\r'), out[i-1], "output: %q", out)
			}
		}
	})
}

func TestExplicitNullAndYAMLSetAreNotCoercedToMappings(t *testing.T) {
	inputs := [][]byte{
		[]byte("a: !!null\nkeep: yes\n"),
		[]byte("s: !!set\n  ? a\n  ? b\nkeep: yes\n"),
	}
	for _, input := range inputs {
		doc, err := Parse(input)
		require.NoError(t, err)
		out, err := Marshal(doc)
		require.NoError(t, err)
		require.Equal(t, input, out)
	}
}

func TestNamedSequenceDeletionReusesPresentedItemBytes(t *testing.T) {
	input := []byte("items:\n  - name: one\n    value: 'quoted' # retain\n  - name: two\n    value: plain\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"remove","path":"/items/1"}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Contains(t, string(out), "value: 'quoted' # retain")
	require.NotContains(t, string(out), "name: two")
}

func TestSequenceInsertionRebasesPriorItemDeletion(t *testing.T) {
	doc, err := Parse([]byte("items:\n  - a: keep\n  - b: remove\n"))
	require.NoError(t, err)
	items := doc.Content[0].Content[1]
	DeleteKey(items.Content[1], "b")
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[{"op":"add","path":"/items/0","value":{"new":"first"}}]`)))
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got struct {
		Items []map[string]string `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Len(t, got.Items, 3)
	require.Equal(t, "first", got.Items[0]["new"])
	require.NotContains(t, got.Items[2], "b")
}
