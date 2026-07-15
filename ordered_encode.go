package yamledit

import (
	"bytes"
	"encoding/json"
	"fmt"
	"sort"
	"strconv"
	"strings"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

// orderedToYAMLNode converts an interface{} value into a yaml.v3 Node while preserving
// ordering for gyaml.MapSlice (and recursively for nested MapSlices).
func orderedToYAMLNode(v interface{}) *yaml.Node {
	switch t := v.(type) {
	case nil:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!null", Value: "null"}
	case bool:
		if t {
			return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!bool", Value: "true"}
		}
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!bool", Value: "false"}
	case int:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.Itoa(t)}
	case int64:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatInt(t, 10)}
	case uint:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatUint(uint64(t), 10)}
	case uint8:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatUint(uint64(t), 10)}
	case uint16:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatUint(uint64(t), 10)}
	case uint32:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatUint(uint64(t), 10)}
	case uint64:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!int", Value: strconv.FormatUint(t, 10)}
	case float64:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!float", Value: formatYAMLFloat(t)}
	case json.Number:
		tag := "!!int"
		if strings.ContainsAny(string(t), ".eE") {
			tag = "!!float"
		}
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: tag, Value: string(t)}
	case string:
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: t}

	case []interface{}:
		seq := &yaml.Node{Kind: yaml.SequenceNode, Tag: "!!seq"}
		for _, e := range t {
			seq.Content = append(seq.Content, orderedToYAMLNode(e))
		}
		return seq

	case gyaml.MapSlice:
		mp := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
		for _, it := range t {
			ks := fmt.Sprint(it.Key)
			mp.Content = append(mp.Content,
				&yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: ks},
				orderedToYAMLNode(it.Value),
			)
		}
		return mp

	// Unordered maps: keep stable ordering (sorted) to avoid nondeterminism.
	// (Not ideal, but better than random. Your primary churn bug is MapSlice -> map conversion,
	// so this case should be rare in the fallback path.)
	case map[string]interface{}:
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		mp := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
		for _, k := range keys {
			mp.Content = append(mp.Content,
				&yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: k},
				orderedToYAMLNode(t[k]),
			)
		}
		return mp

	default:
		// Best-effort scalar string
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: fmt.Sprint(t)}
	}
}

// encodeNodeLines encodes a yaml node to lines, stripping any leading '---' document marker.
func encodeNodeLines(n *yaml.Node, indent int) ([]string, bool) {
	var buf bytes.Buffer
	enc := yaml.NewEncoder(&buf)
	enc.SetIndent(indent)
	if err := enc.Encode(n); err != nil {
		_ = enc.Close()
		return nil, false
	}
	if err := enc.Close(); err != nil {
		return nil, false
	}

	// Remove only the encoder's document-terminating newline. Additional
	// trailing newlines can be significant content in a |+ block scalar.
	s := strings.TrimSuffix(buf.String(), "\n")
	if s == "" {
		return []string{}, true
	}
	lines := strings.Split(s, "\n")
	if len(lines) > 0 && strings.TrimSpace(lines[0]) == "---" {
		lines = lines[1:]
	}
	return lines, true
}
