package yamledit

import (
	"fmt"
	"testing"

	"gopkg.in/yaml.v3"
)

var benchmarkSequencePresentationSink *yaml.Node

func BenchmarkReconcileReplacementPresentationSequence(b *testing.B) {
	for _, size := range []int{256, 1024, 4096} {
		b.Run(fmt.Sprintf("Records%d", size), func(b *testing.B) {
			oldSequence := benchmarkPresentationSequence(size, false)
			newSequence := benchmarkPresentationSequence(size, true)
			b.ReportAllocs()
			b.ResetTimer()
			for b.Loop() {
				reconcileReplacementPresentation(oldSequence, newSequence)
			}
			benchmarkSequencePresentationSink = newSequence
		})
	}
}

// benchmarkPresentationSequence builds the replacement nodes directly so this
// benchmark isolates presentation reconciliation from YAML parsing. Reversing
// the replacement sequence exercises name-based matching independently of the
// item index.
func benchmarkPresentationSequence(size int, reverse bool) *yaml.Node {
	sequence := &yaml.Node{Kind: yaml.SequenceNode, Tag: "!!seq"}
	for position := 0; position < size; position++ {
		index := position
		if reverse {
			index = size - position - 1
		}
		name := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: "name"}
		nameValue := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: fmt.Sprintf("record-%06d", index)}
		value := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: "value"}
		valueValue := &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: fmt.Sprintf("%d", index)}
		record := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
		if reverse {
			record.Content = []*yaml.Node{value, valueValue, name, nameValue}
		} else {
			record.Content = []*yaml.Node{name, nameValue, value, valueValue}
		}
		sequence.Content = append(sequence.Content, record)
	}
	return sequence
}
