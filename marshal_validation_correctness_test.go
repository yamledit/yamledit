package yamledit

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

func TestMarshalRejectsMalformedUnregisteredDocumentsWithoutPanicOrLoss(t *testing.T) {
	key := func(value string) *yaml.Node {
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: value}
	}
	value := func(value string) *yaml.Node {
		return &yaml.Node{Kind: yaml.ScalarNode, Tag: "!!str", Value: value}
	}
	document := func(root *yaml.Node) *yaml.Node {
		return &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{root}}
	}

	tests := []struct {
		name    string
		doc     *yaml.Node
		message string
	}{
		{name: "nil document", doc: nil, message: "exactly one YAML root"},
		{name: "mapping without document", doc: &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}, message: "DocumentNode"},
		{name: "empty document", doc: &yaml.Node{Kind: yaml.DocumentNode}, message: "exactly one YAML root"},
		{
			name: "multiple roots",
			doc: &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{
				{Kind: yaml.MappingNode, Tag: "!!map"},
				{Kind: yaml.MappingNode, Tag: "!!map"},
			}},
			message: "exactly one YAML root",
		},
		{name: "scalar root", doc: document(value("not-a-map")), message: "root is not a mapping"},
		{
			// yaml.v3 silently encoded this malformed mapping as {} before the
			// entry validator was added.
			name:    "unmatched mapping key",
			doc:     document(&yaml.Node{Kind: yaml.MappingNode, Tag: "!!map", Content: []*yaml.Node{key("lost")}}),
			message: "malformed YAML mapping node",
		},
		{
			// yaml.v3 dereferences this nil value while encoding.
			name: "nil mapping value",
			doc: document(&yaml.Node{Kind: yaml.MappingNode, Tag: "!!map", Content: []*yaml.Node{
				key("panic"), nil,
			}}),
			message: "malformed YAML mapping node",
		},
		{
			name: "nil sequence child",
			doc: document(&yaml.Node{Kind: yaml.MappingNode, Tag: "!!map", Content: []*yaml.Node{
				key("items"), {Kind: yaml.SequenceNode, Tag: "!!seq", Content: []*yaml.Node{nil}},
			}}),
			message: "malformed YAML sequence node",
		},
		{
			name: "scalar with ignored content",
			doc: document(&yaml.Node{Kind: yaml.MappingNode, Tag: "!!map", Content: []*yaml.Node{
				key("value"), {Kind: yaml.ScalarNode, Tag: "!!str", Value: "kept", Content: []*yaml.Node{value("lost")}},
			}}),
			message: "malformed YAML scalar node",
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			require.NotPanics(t, func() {
				_, err := Marshal(test.doc)
				require.ErrorContains(t, err, test.message)
			})
		})
	}
}

func TestMarshalRejectsContentCyclesButAllowsRecursiveAliases(t *testing.T) {
	t.Run("content cycle", func(t *testing.T) {
		sequence := &yaml.Node{Kind: yaml.SequenceNode, Tag: "!!seq"}
		sequence.Content = []*yaml.Node{sequence}
		doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{{
			Kind: yaml.MappingNode,
			Tag:  "!!map",
			Content: []*yaml.Node{
				{Kind: yaml.ScalarNode, Tag: "!!str", Value: "items"}, sequence,
			},
		}}}

		require.NotPanics(t, func() {
			_, err := Marshal(doc)
			require.ErrorContains(t, err, "Content graph contains a cycle")
		})
	})

	t.Run("recursive alias", func(t *testing.T) {
		root := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map", Anchor: "root"}
		alias := &yaml.Node{Kind: yaml.AliasNode, Value: "root", Alias: root}
		root.Content = []*yaml.Node{
			{Kind: yaml.ScalarNode, Tag: "!!str", Value: "self"}, alias,
		}
		doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{root}}

		out, err := Marshal(doc)
		require.NoError(t, err)
		var reparsed yaml.Node
		require.NoError(t, yaml.Unmarshal(out, &reparsed), "output:\n%s", out)
		resultRoot := reparsed.Content[0]
		require.Equal(t, "root", resultRoot.Anchor)
		require.Same(t, resultRoot, resultRoot.Content[1].Alias)
	})
}

func TestMarshalRejectsInvalidUTF8InUnregisteredAST(t *testing.T) {
	doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{{
		Kind: yaml.MappingNode,
		Tag:  "!!map",
		Content: []*yaml.Node{
			{Kind: yaml.ScalarNode, Tag: "!!str", Value: "value"},
			{Kind: yaml.ScalarNode, Tag: "!!str", Value: string([]byte{0xff})},
		},
	}}}

	_, err := Marshal(doc)
	require.ErrorContains(t, err, "invalid UTF-8")
}

func TestMarshalRejectsAliasPointerThatSerializedNameCannotRepresent(t *testing.T) {
	input := []byte("first: &same value\nsecond: &same value\nref: *same\n")
	doc, err := Parse(input)
	require.NoError(t, err)
	root := doc.Content[0]
	require.Same(t, root.Content[3], root.Content[5].Alias)

	unchanged, err := Marshal(doc)
	require.NoError(t, err)
	require.Equal(t, input, unchanged)

	// Alias events serialize only *same, which YAML resolves to the most recent
	// preceding &same (second). Retargeting the pointer to first cannot be
	// represented without renaming anchors, so Marshal must not claim success.
	root.Content[5].Alias = root.Content[1]
	_, err = Marshal(doc)
	require.ErrorContains(t, err, "serialized name would not select")
}

func TestMarshalRejectsNodeFieldsThatYAMLEncoderWouldSilentlyIgnore(t *testing.T) {
	t.Run("document metadata", func(t *testing.T) {
		doc := &yaml.Node{
			Kind:        yaml.DocumentNode,
			LineComment: "silently ignored",
			Content:     []*yaml.Node{{Kind: yaml.MappingNode, Tag: "!!map"}},
		}

		_, err := Marshal(doc)
		require.ErrorContains(t, err, "document node has fields the encoder cannot represent")
	})

	t.Run("alias metadata", func(t *testing.T) {
		for _, mutate := range []func(*yaml.Node){
			func(alias *yaml.Node) { alias.Tag = "!Ignored" },
			func(alias *yaml.Node) { alias.Anchor = "ignored" },
			func(alias *yaml.Node) { alias.Style = yaml.DoubleQuotedStyle },
		} {
			doc, err := Parse([]byte("base: &base value\nref: *base\n"))
			require.NoError(t, err)
			mutate(doc.Content[0].Content[3])

			_, err = Marshal(doc)
			require.ErrorContains(t, err, "alias node has fields the encoder cannot represent")
		}
	})

	t.Run("collection value", func(t *testing.T) {
		doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{{
			Kind:  yaml.MappingNode,
			Tag:   "!!map",
			Value: "silently ignored",
		}}}

		_, err := Marshal(doc)
		require.ErrorContains(t, err, "mapping node has fields the encoder cannot represent")
	})

	t.Run("conflicting scalar styles", func(t *testing.T) {
		doc := &yaml.Node{Kind: yaml.DocumentNode, Content: []*yaml.Node{{
			Kind: yaml.MappingNode,
			Tag:  "!!map",
			Content: []*yaml.Node{
				{Kind: yaml.ScalarNode, Tag: "!!str", Value: "value"},
				{
					Kind:  yaml.ScalarNode,
					Tag:   "!!str",
					Value: "ambiguous",
					Style: yaml.SingleQuotedStyle | yaml.DoubleQuotedStyle,
				},
			},
		}}}

		_, err := Marshal(doc)
		require.ErrorContains(t, err, "conflicting styles")
	})
}

func TestRegisteredSettersDoNotPanicOnMalformedDirectAST(t *testing.T) {
	mutations := []struct {
		name   string
		mutate func(*yaml.Node)
	}{
		{name: "nil key", mutate: func(root *yaml.Node) { root.Content[0] = nil }},
		{name: "nil value", mutate: func(root *yaml.Node) { root.Content[1] = nil }},
	}
	for _, mutation := range mutations {
		t.Run(mutation.name, func(t *testing.T) {
			doc, err := Parse([]byte("value: old\n"))
			require.NoError(t, err)
			root := doc.Content[0]
			mutation.mutate(root)

			require.NotPanics(t, func() {
				SetScalarString(root, "other", "new")
				DeleteKey(root, "value")
				_ = EnsurePath(root, "nested")
			})
			require.NotPanics(t, func() {
				_, _ = Marshal(doc)
			})
		})
	}
}

func TestRegisteredOwnershipLookupToleratesMalformedContentCycle(t *testing.T) {
	doc, err := Parse([]byte("cycle: []\nnormal:\n  value: old\n"))
	require.NoError(t, err)
	root := doc.Content[0]
	cycle := mappingValueForStringKey(t, root, "cycle")
	normal := mappingValueForStringKey(t, root, "normal")
	cycle.Content = []*yaml.Node{cycle}

	runSetter := func(target *yaml.Node, key, value string) {
		done := make(chan struct{})
		go func() {
			defer close(done)
			SetScalarString(target, key, value)
		}()
		select {
		case <-done:
		case <-time.After(2 * time.Second):
			t.Fatal("setter hung while ownership lookup traversed a malformed Content cycle")
		}
	}

	// An unrelated standalone handle forces both registered-owner scans. It must
	// still be treated as standalone after the malformed registered graph is
	// skipped, rather than hanging in its cyclic Content edge.
	unrelated := &yaml.Node{Kind: yaml.MappingNode, Tag: "!!map"}
	runSetter(unrelated, "standalone", "yes")
	require.Equal(t, "yes", mappingValueForStringKey(t, unrelated, "standalone").Value)

	// A valid handle later in the same malformed registered tree must remain
	// discoverable, even when a cyclic sibling is visited first.
	runSetter(normal, "value", "new")
	require.Equal(t, "new", mappingValueForStringKey(t, normal, "value").Value)

	// Normal registered lookup and marshaling also continue to work while the
	// malformed document remains present in the global weak registry.
	validDoc, err := Parse([]byte("nested:\n  value: old\n"))
	require.NoError(t, err)
	validNested := mappingValueForStringKey(t, validDoc.Content[0], "nested")
	runSetter(validNested, "value", "new")
	out, err := Marshal(validDoc)
	require.NoError(t, err)
	require.Equal(t, "nested:\n  value: new\n", string(out))
}
