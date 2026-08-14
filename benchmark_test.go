package yamledit

import (
	"fmt"
	"strings"
	"testing"

	"gopkg.in/yaml.v3"
)

type benchmarkFixture struct {
	name string
	data []byte
}

var (
	benchmarkFixtures = []benchmarkFixture{
		{name: "Small", data: benchmarkSmallDocument()},
		{name: "Large", data: benchmarkLargeDocument()},
	}
	benchmarkBytesSink []byte
	benchmarkNodeSink  *yaml.Node

	benchmarkResources = map[string]any{
		"requests": map[string]any{
			"cpu":    "500m",
			"memory": "512Mi",
		},
		"limits": map[string]any{
			"cpu":    "2",
			"memory": "1Gi",
		},
	}
	benchmarkEndpoints = []any{
		map[string]any{"name": "http", "path": "/api", "port": 8080},
		map[string]any{"name": "metrics", "path": "/metrics", "port": 9090},
		map[string]any{"name": "admin", "path": "/admin", "port": 8081},
	}
	benchmarkPatch = []byte(`[
		{"op":"replace","path":"/service/replicas","value":6},
		{"op":"replace","path":"/service/image","value":"registry.example.com/checkout:v2.4.0"},
		{"op":"add","path":"/service/endpoints/-","value":{"name":"admin","path":"/admin","port":8081}}
	]`)
)

func BenchmarkParse(b *testing.B) {
	for _, fixture := range benchmarkFixtures {
		fixture := fixture
		b.Run(fixture.name, func(b *testing.B) {
			b.ReportAllocs()
			b.SetBytes(int64(len(fixture.data)))
			for i := 0; i < b.N; i++ {
				doc, err := Parse(fixture.data)
				if err != nil {
					b.Fatal(err)
				}
				benchmarkNodeSink = doc
			}
		})
	}
}

func BenchmarkMarshalNoOp(b *testing.B) {
	for _, fixture := range benchmarkFixtures {
		fixture := fixture
		b.Run(fixture.name, func(b *testing.B) {
			doc, err := Parse(fixture.data)
			if err != nil {
				b.Fatal(err)
			}

			b.ReportAllocs()
			b.SetBytes(int64(len(fixture.data)))
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				out, err := Marshal(doc)
				if err != nil {
					b.Fatal(err)
				}
				benchmarkBytesSink = out
			}
		})
	}
}

func BenchmarkScalarSurgery(b *testing.B) {
	for _, fixture := range benchmarkFixtures {
		fixture := fixture
		b.Run(fixture.name, func(b *testing.B) {
			benchmarkEditAndMarshal(b, fixture.data, func(b *testing.B, doc *yaml.Node) {
				service := benchmarkMapAt(doc.Content[0], "service")
				if service == nil {
					b.Fatal("service mapping not found")
				}
				SetScalarInt(service, "replicas", 6)
			})
		})
	}
}

func BenchmarkStructuralEdit(b *testing.B) {
	for _, fixture := range benchmarkFixtures {
		fixture := fixture
		b.Run(fixture.name, func(b *testing.B) {
			benchmarkEditAndMarshal(b, fixture.data, func(b *testing.B, doc *yaml.Node) {
				service := benchmarkMapAt(doc.Content[0], "service")
				if service == nil {
					b.Fatal("service mapping not found")
				}
				SetValue(service, "resources", benchmarkResources, SetValueOptions{SortKeys: true})
			})
		})
	}
}

func BenchmarkSequenceEdit(b *testing.B) {
	for _, fixture := range benchmarkFixtures {
		fixture := fixture
		b.Run(fixture.name, func(b *testing.B) {
			benchmarkEditAndMarshal(b, fixture.data, func(b *testing.B, doc *yaml.Node) {
				service := benchmarkMapAt(doc.Content[0], "service")
				if service == nil {
					b.Fatal("service mapping not found")
				}
				SetValue(service, "endpoints", benchmarkEndpoints, SetValueOptions{SortKeys: true})
			})
		})
	}
}

func BenchmarkJSONPatch(b *testing.B) {
	for _, fixture := range benchmarkFixtures {
		fixture := fixture
		b.Run(fixture.name, func(b *testing.B) {
			benchmarkEditAndMarshal(b, fixture.data, func(b *testing.B, doc *yaml.Node) {
				if err := ApplyJSONPatchBytes(doc, benchmarkPatch); err != nil {
					b.Fatal(err)
				}
			})
		})
	}
}

func BenchmarkReconcileReplacementPresentationFlatMapping(b *testing.B) {
	for _, entries := range []int{128, 1024, 8192} {
		b.Run(fmt.Sprintf("Entries%d", entries), func(b *testing.B) {
			oldNode := benchmarkFlatMapping(entries, false)
			newNode := benchmarkFlatMapping(entries, true)
			b.ReportAllocs()
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				reconcileReplacementPresentation(oldNode, newNode)
			}
		})
	}
}

func benchmarkFlatMapping(entries int, reverse bool) *yaml.Node {
	node := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
	for position := 0; position < entries; position++ {
		index := position
		if reverse {
			index = entries - position - 1
		}
		value := fmt.Sprintf("entry-%06d", index)
		node.Content = append(node.Content,
			&yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: value},
			&yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: value},
		)
	}
	return node
}

// benchmarkEditAndMarshal excludes fixture parsing from the timed region. Each
// benchmark closure includes whatever public-path lookup its operation needs;
// the edit and its validated Marshal are measured together because source
// surgery and scoped structural rendering are performed lazily by Marshal.
func benchmarkEditAndMarshal(b *testing.B, source []byte, edit func(*testing.B, *yaml.Node)) {
	b.Helper()
	b.ReportAllocs()
	b.SetBytes(int64(len(source)))
	b.StopTimer()
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		doc, err := Parse(source)
		if err != nil {
			b.Fatal(err)
		}
		b.StartTimer()

		edit(b, doc)
		out, err := Marshal(doc)

		b.StopTimer()
		if err != nil {
			b.Fatal(err)
		}
		benchmarkBytesSink = out
	}
}

func benchmarkMapAt(root *yaml.Node, path ...string) *yaml.Node {
	current := root
	for _, key := range path {
		if current == nil || current.Kind != yaml.MappingNode {
			return nil
		}
		var next *yaml.Node
		for i := len(current.Content) - 2; i >= 0; i -= 2 {
			if isStringMappingKey(current.Content[i], key) {
				next = current.Content[i+1]
				break
			}
		}
		current = next
	}
	if current == nil || current.Kind != yaml.MappingNode {
		return nil
	}
	return current
}

func benchmarkSmallDocument() []byte {
	return []byte(`# checkout deployment
service:
  name: checkout
  replicas: 3 # autoscaler floor
  enabled: true
  image: registry.example.com/checkout:v2.3.1
  resources:
    requests:
      cpu: 250m
      memory: 256Mi
    limits:
      cpu: "1"
      memory: 512Mi
  endpoints:
    - name: http
      path: /api
      port: 8080
    - name: metrics
      path: /metrics
      port: 9090
metadata:
  owner: payments-platform
  environment: production
  annotations:
    runbook: https://example.com/runbooks/checkout
`)
}

func benchmarkLargeDocument() []byte {
	var out strings.Builder
	out.Grow(160 << 10)
	out.Write(benchmarkSmallDocument())
	out.WriteString("pipelines:\n")
	for i := 0; i < 240; i++ {
		fmt.Fprintf(&out, `  - name: event-pipeline-%03d
    enabled: true
    source:
      topic: events.%03d
      consumerGroup: checkout-worker-%03d
    processors:
      - name: normalize
        kind: transform
        expression: |
          .payload.account_id = string!(.payload.account_id)
          .metadata.pipeline = "event-pipeline-%03d"
      - name: validate
        kind: schema
        schema: checkout-event-v2
    sink:
      type: kafka
      topic: normalized.%03d
      retries: 5
      timeout: 10s
`, i, i, i, i, i)
	}
	return []byte(out.String())
}
