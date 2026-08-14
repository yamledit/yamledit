package yamledit

import (
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestReconcileReplacementPresentationSequenceMatchesUniqueNameAcrossIndexes(t *testing.T) {
	oldSequence := mustUnmarshalSequence(t, `
- name: one
  value: keep
- name: "two" # source-name
  value: 'old' # source-value
`)
	newSequence := mustUnmarshalSequence(t, `
- value: changed
  name: two
- value: retained
  name: one
`)

	reconcileReplacementPresentation(oldSequence, newSequence)

	record := newSequence.Content[0]
	require.Equal(t, []string{"name", "value"}, stringMappingKeys(record))
	require.Equal(t, "two", record.Content[1].Value)
	require.Equal(t, yaml.DoubleQuotedStyle, record.Content[1].Style)
	require.Equal(t, "# source-name", record.Content[1].LineComment)
	require.Equal(t, "changed", record.Content[3].Value)
	require.Equal(t, "# source-value", record.Content[3].LineComment)
}

func TestReconcileReplacementPresentationSequenceDoesNotChooseAmbiguousName(t *testing.T) {
	oldSequence := mustUnmarshalSequence(t, `
- name: "duplicate" # first
  value: one
- name: 'duplicate' # second
  value: two
`)
	newSequence := mustUnmarshalSequence(t, `
- value: replacement
  name: duplicate
`)

	reconcileReplacementPresentation(oldSequence, newSequence)

	record := newSequence.Content[0]
	require.Equal(t, []string{"name", "value"}, stringMappingKeys(record), "the mapping template still controls field order")
	require.Equal(t, yaml.Style(0), record.Content[1].Style)
	require.Empty(t, record.Content[1].LineComment, "neither ambiguous occurrence may donate presentation")
}

func TestReconcileReplacementPresentationSequenceUsesUniqueNameOnlyOnce(t *testing.T) {
	oldSequence := mustUnmarshalSequence(t, `
- name: "same" # source
  value: old
`)
	newSequence := mustUnmarshalSequence(t, `
- value: first
  name: same
- value: second
  name: same
`)

	reconcileReplacementPresentation(oldSequence, newSequence)

	first := newSequence.Content[0]
	require.Equal(t, []string{"name", "value"}, stringMappingKeys(first))
	require.Equal(t, yaml.DoubleQuotedStyle, first.Content[1].Style)
	require.Equal(t, "# source", first.Content[1].LineComment)

	second := newSequence.Content[1]
	require.Equal(t, []string{"value", "name"}, stringMappingKeys(second))
	require.Equal(t, yaml.Style(0), second.Content[3].Style)
	require.Empty(t, second.Content[3].LineComment, "one source occurrence must not donate presentation twice")
}

func TestReconcileReplacementPresentationSequenceMatchesUniqueLogicalValue(t *testing.T) {
	oldSequence := mustUnmarshalSequence(t, `
- keep
- "same" # source
`)
	newSequence := mustUnmarshalSequence(t, `
- same
- keep
`)

	reconcileReplacementPresentation(oldSequence, newSequence)

	require.Equal(t, yaml.DoubleQuotedStyle, newSequence.Content[0].Style)
	require.Equal(t, "# source", newSequence.Content[0].LineComment)
}

func TestReconcileReplacementPresentationSequenceDoesNotChooseAmbiguousLogicalValue(t *testing.T) {
	oldSequence := mustUnmarshalSequence(t, `
- "same" # first
- 'same' # second
`)
	newSequence := mustUnmarshalSequence(t, `
- same
`)

	reconcileReplacementPresentation(oldSequence, newSequence)

	require.Equal(t, yaml.Style(0), newSequence.Content[0].Style)
	require.Empty(t, newSequence.Content[0].LineComment)
}

func TestReconcileReplacementPresentationFingerprintUsesLogicalNumberEquality(t *testing.T) {
	oldSequence := mustUnmarshalSequence(t, `
- !!int 1 # source
`)
	newSequence := mustUnmarshalSequence(t, `
- !!float 1.0
`)

	reconcileReplacementPresentation(oldSequence, newSequence)

	require.Equal(t, "!!float", newSequence.Content[0].Tag)
	require.Equal(t, "# source", newSequence.Content[0].LineComment)
}

func mustUnmarshalSequence(t *testing.T, input string) *yaml.Node {
	t.Helper()
	var document yaml.Node
	require.NoError(t, yaml.Unmarshal([]byte(input), &document))
	require.NotEmpty(t, document.Content)
	sequence := document.Content[0]
	require.Equal(t, yaml.SequenceNode, sequence.Kind)
	return sequence
}

func stringMappingKeys(node *yaml.Node) []string {
	keys := make([]string, 0, len(node.Content)/2)
	for index := 0; index+1 < len(node.Content); index += 2 {
		keys = append(keys, node.Content[index].Value)
	}
	return keys
}
