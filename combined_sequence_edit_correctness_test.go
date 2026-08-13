package yamledit

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestSequenceAppendComposesWithExistingMappingScalarReplacement(t *testing.T) {
	input := "items:\n  - name: one # keep identity comment\n    value: old\n    keep: 'styled'\n"
	doc, err := Parse([]byte(input))
	require.NoError(t, err)
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[
		{"op":"replace","path":"/items/0/value","value":"new"}
	]`)))
	require.NoError(t, ApplyJSONPatchBytes(doc, []byte(`[
		{"op":"add","path":"/items/-","value":{"name":"two","value":"added"}}
	]`)))

	out, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, "items:\n  - name: one # keep identity comment\n    value: new\n    keep: 'styled'\n  - name: two\n    value: added\n", string(out))
	requireSequenceEditAndAppendSemantics(t, out, "new")
}

func TestSequenceAppendComposesWithPresentedMappingScalarReplacement(t *testing.T) {
	tests := []struct {
		name  string
		input string
		value any
		want  string
	}{
		{
			name:  "literal block to JSON number",
			input: "items:\n  - name: \"one\" # keep identity comment\n    value: |\n      old\n    keep: 'styled'\n",
			value: 7,
			want:  "7",
		},
		{
			name:  "literal block to JSON string",
			input: "items:\n  - name: \"one\" # keep identity comment\n    value: |\n      old\n    keep: 'styled'\n",
			value: "new",
			want:  "new",
		},
		{
			name:  "double quoted flow scalar",
			input: "items:\n  - name: \"one\" # keep identity comment\n    value: \"old\"\n    keep: 'styled'\n",
			value: "new",
			want:  `"new"`,
		},
		{
			name:  "multiline double quoted flow scalar",
			input: "items:\n  - name: \"one\" # keep identity comment\n    value: \"old\n      folded\"\n    keep: 'styled'\n",
			value: "new",
			want:  "new",
		},
		{
			name:  "multiline single quoted flow scalar",
			input: "items:\n  - name: \"one\" # keep identity comment\n    value: 'old\n      folded'\n    keep: 'styled'\n",
			value: "new",
			want:  "new",
		},
		{
			name:  "multiline plain flow scalar",
			input: "items:\n  - name: \"one\" # keep identity comment\n    value: old\n      folded\n    keep: 'styled'\n",
			value: "new",
			want:  "new",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			doc, err := Parse([]byte(tt.input))
			require.NoError(t, err)
			valueJSON, err := json.Marshal(tt.value)
			require.NoError(t, err)
			patch := []byte("[\n" +
				`{"op":"replace","path":"/items/0/value","value":` + string(valueJSON) + "},\n" +
				`{"op":"add","path":"/items/-","value":{"name":"two","value":"added"}}` + "\n]")
			require.NoError(t, ApplyJSONPatchBytes(doc, patch))

			out, err := Marshal(doc)
			require.NoError(t, err)
			expected := "items:\n  - name: \"one\" # keep identity comment\n    value: " + tt.want + "\n    keep: 'styled'\n  - name: two\n    value: added\n"
			require.Equal(t, expected, string(out))
			requireSequenceEditAndAppendSemantics(t, out, tt.value)
		})
	}
}

func requireSequenceEditAndAppendSemantics(t *testing.T, output []byte, want any) {
	t.Helper()
	var decoded struct {
		Items []map[string]any `yaml:"items"`
	}
	require.NoError(t, yaml.Unmarshal(output, &decoded), "output:\n%s", output)
	require.Len(t, decoded.Items, 2, "output:\n%s", output)
	require.Equal(t, want, decoded.Items[0]["value"], "output:\n%s", output)
	require.Equal(t, "styled", decoded.Items[0]["keep"], "output:\n%s", output)
	require.Equal(t, "two", decoded.Items[1]["name"], "output:\n%s", output)
	require.Equal(t, "added", decoded.Items[1]["value"], "output:\n%s", output)
}
