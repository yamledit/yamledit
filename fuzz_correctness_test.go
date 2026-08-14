package yamledit

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math"
	"strings"
	"testing"
	"unicode/utf8"

	jsonpatch "github.com/evanphx/json-patch/v5"
	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

const (
	fuzzMaxYAMLBytes    = 16 << 10
	fuzzMaxPatchBytes   = 8 << 10
	fuzzMaxHistoryBytes = 64
)

// FuzzParseMarshalNoop exercises the broad parser surface independently of the
// mutators. Ordinary source must be byte-stable; documented duplicate-key and
// implicit-map normalization is checked semantically. Marshal must never
// mutate the caller's AST. Empty input synthesizes an empty mapping.
func FuzzParseMarshalNoop(f *testing.F) {
	seeds := [][]byte{
		nil,
		[]byte("{}"),
		[]byte("{}\n"),
		[]byte("# comments only\n\n"),
		[]byte("plain: value\nnumber: 1.0\nboolean: true\nnull: null\n"),
		[]byte("quoted: \"first\n  second: still text\"\ntail: keep\n"),
		[]byte("literal: |-\n  first\n  second: value\nfolded: >+\n  third\n  fourth\n"),
		[]byte("flow: {first: [1, 2,\n  3], second: {nested: true}}\ntail: keep\n"),
		[]byte("base: &base {x: 1, nested: [a, b]}\nalias: *base\n"),
		[]byte("first: &shared\n  value: one\nsecond:\n  copy: *shared\n"),
		[]byte("duplicate: one # first\nduplicate: two # second\ntail: keep\n"),
		// yaml.v3 and goccy historically disagreed on this compact spelling;
		// the returned yaml.Node must remain the authoritative interpretation.
		[]byte("A: {0:}"),
		[]byte("A: &0000 {0:}"),
		[]byte("00A: &base {0000:00,000A: [A,A]}#00000000"),
		[]byte("items:\n  - name: one\n    value: !!str\n      plain continuation\n  - {name: two, value: [a, b]}\n"),
		[]byte("implicit:\nexplicit: !!null ''\ntail: keep\n"),
		[]byte("!Config\nname: demo\nvalue: !Custom tagged\n"),
		[]byte("windows: true\r\nitems:\r\n  - one\r\n  - two\r\n"),
		append([]byte{0xef, 0xbb, 0xbf}, []byte("bom: present\n")...),
	}
	for _, seed := range seeds {
		f.Add(seed)
	}

	f.Fuzz(func(t *testing.T, source []byte) {
		if len(source) > fuzzMaxYAMLBytes {
			return
		}
		sourceGraph := fuzzDecodeSourceGraph(source)
		doc, err := Parse(source)
		if err != nil {
			return
		}

		before := cloneYAMLNodeGraph(doc)
		out, err := Marshal(doc)
		if !yamlNodeGraphEqual(doc, before) {
			t.Fatal("no-op Marshal mutated the parsed YAML graph")
		}
		if err != nil {
			// Parse intentionally materializes implicit empty mapping values and
			// safely collapses duplicate keys. Some exotic layouts have no scoped
			// byte rewrite for that normalization; the documented explicit error is
			// acceptable, whereas an ordinary no-op document must always marshal.
			if fuzzSourceMayNormalize(source) {
				return
			}
			t.Fatalf("Parse accepted input that no-op Marshal rejected: %v\ninput:\n%q", err, source)
		}
		if len(source) != 0 && !fuzzSourceMayNormalize(source) && !bytes.Equal(out, source) {
			t.Fatalf("no-op Marshal changed source bytes\ninput:  %q\noutput: %q", source, out)
		}

		roundTrip, err := Parse(out)
		if err != nil {
			t.Fatalf("Marshal produced YAML that Parse rejected: %v\noutput:\n%q", err, out)
		}
		assertFuzzGraphMatch(t, doc, roundTrip, sourceGraph, fuzzSourceMayNormalize(source), "no-op Marshal", out)
		second, err := Marshal(roundTrip)
		if err != nil {
			t.Fatalf("second no-op Marshal failed: %v\noutput:\n%q", err, out)
		}
		if !bytes.Equal(second, out) {
			t.Fatalf("Parse/Marshal did not reach a stable representation\nfirst:  %q\nsecond: %q", out, second)
		}
	})
}

// FuzzJSONPatchAtomicAndSemantic feeds both YAML and raw JSON Patch bytes into
// the public API. Failed patches must be graph- and byte-atomic. Successful
// patches are checked against the existing RFC 6902 implementation when both
// inputs are JSON-compatible, then checked again after YAML serialization.
func FuzzJSONPatchAtomicAndSemantic(f *testing.F) {
	seeds := []struct {
		yaml  string
		patch string
	}{
		{"a: 1\nitems: [one, two]\n", `[]`},
		{"a: 1\nitems: [one, two]\n", `[{"op":"replace","path":"/a","value":1.0}]`},
		{"a: 1\nitems: [one, two]\n", `[{"op":"add","path":"/items/-","value":{"nested":true}}]`},
		{"a: 1\nitems: [one, two]\n", `[{"op":"move","from":"/items/0","path":"/items/1"}]`},
		{"a: 1\nitems: [one, two]\n", `[{"op":"copy","from":"/items/0","path":"/copy"}]`},
		{"number: 1e999\n", `[{"op":"test","path":"/number","value":10e998}]`},
		{"base: &base {x: 1, y: two}\nalias: *base\n", `[{"op":"replace","path":"/base/x","value":2}]`},
		{"base: &base {x: 1, y: two}\nalias: *base\n", `[{"op":"copy","from":"/alias","path":"/materialized"}]`},
		{"duplicate: one\nduplicate: two\ntail: keep\n", `[{"op":"replace","path":"/duplicate","value":"new"}]`},
		{"flow: {a: 1,\nb: [2, 3]}\nquoted: \"old\nvalue\"\n", `[{"op":"replace","path":"/flow/b/0","value":4},{"op":"replace","path":"/quoted","value":"new"}]`},
		{"a: 1\n", `[{"op":"add","path":"/b","value":2},{"op":"test","path":"/a","value":99}]`},
		{"a: 1\n", `[{"op":"replace","path":"/a","value":2,"value":3}]`},
		{"a: 1\n", `[{"op":"replace","path":"/a","value":2}] trailing`},
		{"root: {a: 1}\n", `[{"op":"copy","from":"","path":"/snapshot"}]`},
	}
	for _, seed := range seeds {
		f.Add([]byte(seed.yaml), []byte(seed.patch))
	}

	f.Fuzz(func(t *testing.T, source, patchBytes []byte) {
		if len(source) > fuzzMaxYAMLBytes || len(patchBytes) > fuzzMaxPatchBytes {
			return
		}
		sourceGraph := fuzzDecodeSourceGraph(source)
		doc, err := Parse(source)
		if err != nil {
			return
		}
		before := cloneYAMLNodeGraph(doc)
		oracleSource, oracleOK := fuzzJSONDocument(before)
		oracleComparable := oracleOK && fuzzPatchOracleComparable(patchBytes)
		var oracleWant any
		var oracleErr error
		if oracleComparable {
			func() {
				defer func() {
					if recover() != nil {
						oracleComparable = false
					}
				}()
				patch, decodeErr := jsonpatch.DecodePatch(patchBytes)
				if decodeErr != nil {
					oracleErr = decodeErr
					return
				}
				var oracleOutput []byte
				oracleOutput, oracleErr = patch.Apply(oracleSource)
				if oracleErr == nil {
					decoder := json.NewDecoder(bytes.NewReader(oracleOutput))
					decoder.UseNumber()
					if decodeErr := decoder.Decode(&oracleWant); decodeErr != nil {
						t.Fatalf("cannot decode JSON Patch oracle output: %v", decodeErr)
					}
				}
			}()
		}

		err = ApplyJSONPatchBytes(doc, patchBytes)
		if oracleComparable && (err == nil) != (oracleErr == nil) {
			t.Fatalf("JSON Patch success/error mismatch\nsource: %q\npatch:  %q\nyamledit error: %v\noracle error:   %v", source, patchBytes, err, oracleErr)
		}
		if err != nil {
			if !yamlNodeGraphEqual(doc, before) {
				t.Fatalf("failed JSON Patch mutated the YAML graph: %v\npatch: %q", err, patchBytes)
			}
			beforeMarshal := cloneYAMLNodeGraph(doc)
			out, marshalErr := Marshal(doc)
			if !yamlNodeGraphEqual(doc, beforeMarshal) {
				t.Fatal("Marshal mutated the graph after a failed JSON Patch")
			}
			if marshalErr != nil {
				if fuzzSourceMayNormalize(source) {
					return
				}
				t.Fatalf("failed JSON Patch left the document unmarshalable: patch error: %v; marshal error: %v", err, marshalErr)
			}
			if len(source) != 0 && !fuzzSourceMayNormalize(source) && !bytes.Equal(out, source) {
				t.Fatalf("failed JSON Patch changed source bytes\npatch:  %q\ninput:  %q\noutput: %q", patchBytes, source, out)
			}
			roundTrip, parseErr := Parse(out)
			if parseErr != nil {
				t.Fatalf("failed JSON Patch produced unparsable no-op output: %v\noutput: %q", parseErr, out)
			}
			assertFuzzGraphMatch(t, before, roundTrip, sourceGraph, fuzzSourceMayNormalize(source), "failed JSON Patch", out)
			return
		}

		// The production patch engine does not delegate execution to
		// evanphx/json-patch, so this is an independent semantic oracle for the
		// JSON-compatible, duplicate-free overlap of the two APIs.
		if oracleComparable {
			got := yamlNodeToInterface(doc.Content[0])
			if !logicalValueEqual(got, oracleWant) {
				t.Fatalf("JSON Patch semantic mismatch\nsource: %q\npatch:  %q\nwant:   %#v\ngot:    %#v", source, patchBytes, oracleWant, got)
			}
		}

		beforeMarshal := cloneYAMLNodeGraph(doc)
		out, marshalErr := Marshal(doc)
		if !yamlNodeGraphEqual(doc, beforeMarshal) {
			t.Fatal("Marshal mutated a successfully patched YAML graph")
		}
		if marshalErr != nil {
			// Some otherwise-valid source layouts intentionally cannot be edited
			// safely without reformatting. Marshal's explicit error is preferable
			// to accepting output with silent semantic divergence.
			return
		}
		roundTrip, parseErr := Parse(out)
		if parseErr != nil {
			t.Fatalf("patched output cannot be parsed: %v\noutput:\n%q", parseErr, out)
		}
		assertFuzzGraphMatch(t, beforeMarshal, roundTrip, before, fuzzSourceMayNormalize(source), "successful JSON Patch", out)
	})
}

// FuzzBoundedMutationHistory applies a compact instruction stream without
// intermediate marshaling. This stresses composition bugs where individually
// valid edits leave stale source spans, deletion markers, or rewrite intents.
func FuzzBoundedMutationHistory(f *testing.F) {
	for source := range fuzzMutationSources {
		f.Add(uint8(source), []byte{0, 1, 2, 3, 4, 5, 6, 7, 8, 9})
		f.Add(uint8(source), []byte{6, 0, 7, 31, 8, 5, 2})
	}
	// Repeatedly updating a key which has not yet been emitted must not create
	// duplicate zero-width insertion patches.
	f.Add(uint8(5), []byte("10y"))

	f.Fuzz(func(t *testing.T, sourceIndex uint8, history []byte) {
		if len(history) > fuzzMaxHistoryBytes {
			return
		}
		source := fuzzMutationSources[int(sourceIndex)%len(fuzzMutationSources)]
		doc, err := Parse(source)
		if err != nil {
			t.Fatalf("invalid built-in mutation seed: %v\nsource:\n%s", err, source)
		}
		root := doc.Content[0]
		sourceGraph := fuzzDecodeSourceGraph(source)
		keys := [...]string{"target", "extra", "workspace"}
		strings := [...]string{"", "true", "a: b", "#hash", "null", "line\nbreak", " spaced "}
		floats := [...]float64{0, math.Copysign(0, -1), 1, 1.5, -2.25, math.SmallestNonzeroFloat64, math.MaxFloat64}
		jsonValues := [...]string{"null", "true", `"text"`, "1", "1.0", `{"nested":[true,2]}`, `["a",3]`}

		for step, instruction := range history {
			key := keys[int(instruction>>4)%len(keys)]
			switch instruction % 10 {
			case 0:
				SetScalarInt(root, key, int(int8(instruction)))
			case 1:
				SetScalarString(root, key, strings[int(instruction)%len(strings)])
			case 2:
				SetScalarBool(root, key, instruction&0x80 != 0)
			case 3:
				SetScalarFloat(root, key, floats[int(instruction)%len(floats)])
			case 4:
				SetValue(root, key, []any{int8(instruction), strings[int(instruction)%len(strings)], instruction%2 == 0}, SetValueOptions{})
			case 5:
				SetValue(root, key, map[string]any{
					"number": uint64(instruction),
					"nested": []any{json.Number(fmt.Sprintf("%d.0", instruction)), nil},
				}, SetValueOptions{SortKeys: instruction&1 != 0})
			case 6:
				DeleteKey(root, key)
			case 7:
				nested := EnsurePath(doc, "workspace")
				if nested == nil {
					t.Fatalf("step %d: EnsurePath returned nil", step)
				}
				SetValue(nested, "leaf", map[string]any{"step": step, "value": strings[int(instruction)%len(strings)]}, SetValueOptions{SortKeys: true})
			case 8:
				patch := fmt.Sprintf(`[{"op":"add","path":"/%s","value":%s}]`, key, jsonValues[int(instruction)%len(jsonValues)])
				if err := ApplyJSONPatchBytes(doc, []byte(patch)); err != nil {
					t.Fatalf("step %d: generated JSON Patch failed: %v\npatch: %s", step, err, patch)
				}
			case 9:
				SetMapValues(root, map[string]any{
					"extra":   int16(instruction),
					"history": []string{"kept", strings[int(instruction)%len(strings)]},
				}, SetValueOptions{SortKeys: instruction&1 != 0})
			}
		}

		beforeMarshal := cloneYAMLNodeGraph(doc)
		out, err := Marshal(doc)
		if !yamlNodeGraphEqual(doc, beforeMarshal) {
			t.Fatal("Marshal mutated the graph after a bounded mutation history")
		}
		if err != nil {
			// Package-managed edits are deliberately fail-closed when a source
			// layout has no safe scoped rewrite. An explicit error satisfies the
			// correctness invariant; only successful output can be checked for
			// semantic divergence below.
			return
		}
		roundTrip, err := Parse(out)
		if err != nil {
			t.Fatalf("mutation output cannot be parsed: %v\noutput:\n%q", err, out)
		}
		assertFuzzGraphMatch(t, beforeMarshal, roundTrip, sourceGraph, false, "mutation history", out)
		second, err := Marshal(roundTrip)
		if err != nil {
			t.Fatalf("mutation output failed a no-op Marshal: %v", err)
		}
		if !bytes.Equal(second, out) {
			t.Fatalf("mutation output was not byte-stable on reparse\nfirst:  %q\nsecond: %q", out, second)
		}
	})
}

var fuzzMutationSources = [][]byte{
	[]byte("target: old\nkeep: yes\n"),
	[]byte("target: \"old\n  continuation: text\"\nflow: {a: 1,\nb: [2, 3]}\nkeep: yes\n"),
	[]byte("target: |-\n  first\n  second: value\nkeep: yes\n"),
	[]byte("base: &base {x: 1, y: [a, b]}\ntarget: *base\ncopy: *base\nkeep: yes\n"),
	[]byte("target: one # first\ntarget: two # second\nkeep: yes\n"),
	[]byte("target: {old: 1,\n nested: [a, b]}\nkeep: yes\n"),
	[]byte("items:\n  - name: one\n    value: old\ntarget: !!str\n  plain\nkeep: yes\n"),
	[]byte("target: old\r\nitems:\r\n  - one\r\nkeep: yes\r\n"),
}

func fuzzOrderedMap(t *testing.T, doc *yaml.Node) gyaml.MapSlice {
	t.Helper()
	if doc == nil || doc.Kind != yaml.DocumentNode || len(doc.Content) != 1 || doc.Content[0] == nil {
		t.Fatal("expected one YAML mapping document")
	}
	value, err := yamlNodeToOrderedValue(doc.Content[0])
	if err != nil {
		t.Fatalf("cannot project YAML semantics: %v", err)
	}
	mapping, ok := value.(gyaml.MapSlice)
	if !ok {
		t.Fatalf("document root projected as %T, not an ordered mapping", value)
	}
	return mapping
}

func fuzzDecodeSourceGraph(source []byte) *yaml.Node {
	if len(source) == 0 || isYAMLTriviaOnly(source) {
		return nil
	}
	var document yaml.Node
	if err := decodeSingleYAMLDocument(source, &document); err != nil {
		return nil
	}
	return &document
}

// assertFuzzGraphMatch compares the serializable YAML graph rather than only
// its JSON-like values. Mapping order, duplicate multiplicity, kind/tag,
// comments, anchors, styles, and alias targets are all observable contracts.
// Two intentional transformations are modeled narrowly:
//   - earlier duplicate string-key occurrences may be removed (last wins);
//   - nodes changed since sourceGraph may acquire an emitter-chosen scalar style
//     or lose parser coordinates, while untouched nodes must retain presentation.
func assertFuzzGraphMatch(t *testing.T, wantDoc, gotDoc, sourceGraph *yaml.Node, allowNormalizationStyle bool, context string, output []byte) {
	t.Helper()
	if ok, reason := fuzzYAMLGraphEqual(wantDoc, gotDoc, sourceGraph, allowNormalizationStyle); !ok {
		t.Fatalf("%s changed YAML graph during Marshal: %s\noutput:\n%q", context, reason, output)
	}
}

func fuzzYAMLGraphEqual(wantDoc, gotDoc, sourceGraph *yaml.Node, allowNormalizationStyle bool) (bool, string) {
	type comparison struct {
		want             *yaml.Node
		got              *yaml.Node
		path             string
		allowStyleChange bool
	}
	stack := []comparison{{want: wantDoc, got: gotDoc, path: "$", allowStyleChange: allowNormalizationStyle}}
	wantToGot := make(map[*yaml.Node]*yaml.Node)
	gotToWant := make(map[*yaml.Node]*yaml.Node)
	sourceNodes := fuzzIndexSourceNodes(sourceGraph)
	wantComments := make(map[string]int)
	gotComments := make(map[string]int)
	addComments := func(comments map[string]int, node *yaml.Node) {
		for _, comment := range []string{node.HeadComment, node.LineComment, node.FootComment} {
			if comment != "" {
				comments[strings.TrimRight(comment, " \t\r")]++
			}
		}
	}
	for len(stack) > 0 {
		last := len(stack) - 1
		current := stack[last]
		stack = stack[:last]
		want, got := current.want, current.got
		if want == nil || got == nil {
			if want != got {
				return false, current.path + ": nil node mismatch"
			}
			continue
		}
		if mapped, exists := wantToGot[want]; exists {
			if mapped != got {
				return false, current.path + ": one requested node serialized as multiple nodes"
			}
			continue
		}
		if mapped, exists := gotToWant[got]; exists && mapped != want {
			return false, current.path + ": distinct requested nodes serialized as one node"
		}
		wantToGot[want] = got
		gotToWant[got] = want

		if want.Kind != got.Kind || want.Tag != got.Tag || want.Value != got.Value || want.Anchor != got.Anchor {
			return false, fmt.Sprintf("%s: node mismatch want(kind=%d tag=%q value=%q anchor=%q) got(kind=%d tag=%q value=%q anchor=%q)", current.path, want.Kind, want.Tag, want.Value, want.Anchor, got.Kind, got.Tag, got.Value, got.Anchor)
		}
		if allowNormalizationStyle {
			addComments(wantComments, want)
			addComments(gotComments, got)
		} else if want.HeadComment != got.HeadComment || want.LineComment != got.LineComment || want.FootComment != got.FootComment {
			return false, current.path + ": comments changed"
		}
		unchangedFromSource := fuzzNodeUnchangedFromSource(want, sourceNodes)
		if !current.allowStyleChange && unchangedFromSource && want.Style != got.Style {
			return false, current.path + ": scalar or collection style changed"
		}
		allowChildStyleChange := current.allowStyleChange
		if want != wantDoc && want != wantDoc.Content[0] &&
			(want.Kind == yaml.MappingNode || want.Kind == yaml.SequenceNode) && !unchangedFromSource {
			allowChildStyleChange = true
		}

		if want.Kind == yaml.AliasNode {
			if got.Kind != yaml.AliasNode || want.Alias == nil || got.Alias == nil {
				return false, current.path + ": alias topology changed"
			}
			stack = append(stack, comparison{want: want.Alias, got: got.Alias, path: current.path + "->alias", allowStyleChange: allowChildStyleChange})
		}

		wantChildren := nodeContent(want)
		gotChildren := nodeContent(got)
		if want.Kind == yaml.MappingNode && len(wantChildren) != len(gotChildren) {
			// Marshal may remove earlier duplicate string-key occurrences. Never
			// collapse the actual output here: generated duplicates must remain
			// visible to the oracle.
			wantChildren = fuzzRetainedChildren(want)
		}
		if len(wantChildren) != len(gotChildren) {
			return false, fmt.Sprintf("%s: child count changed from %d to %d", current.path, len(wantChildren), len(gotChildren))
		}
		for index := len(wantChildren) - 1; index >= 0; index-- {
			stack = append(stack, comparison{
				want: wantChildren[index], got: gotChildren[index], path: fmt.Sprintf("%s[%d]", current.path, index),
				allowStyleChange: allowChildStyleChange,
			})
		}
	}
	if allowNormalizationStyle {
		if len(wantComments) != len(gotComments) {
			return false, "comment set changed during source normalization"
		}
		for comment, count := range wantComments {
			if gotComments[comment] != count {
				return false, "comment set changed during source normalization"
			}
		}
	}
	return true, ""
}

type fuzzSourcePosition struct {
	kind         yaml.Kind
	line, column int
}

func fuzzIndexSourceNodes(root *yaml.Node) map[fuzzSourcePosition][]*yaml.Node {
	indexed := make(map[fuzzSourcePosition][]*yaml.Node)
	seen := make(map[*yaml.Node]struct{})
	stack := []*yaml.Node{root}
	for len(stack) > 0 {
		last := len(stack) - 1
		node := stack[last]
		stack = stack[:last]
		if node == nil {
			continue
		}
		if _, exists := seen[node]; exists {
			continue
		}
		seen[node] = struct{}{}
		if node.Line > 0 && node.Column > 0 {
			position := fuzzSourcePosition{kind: node.Kind, line: node.Line, column: node.Column}
			indexed[position] = append(indexed[position], node)
		}
		stack = append(stack, node.Content...)
		if node.Alias != nil {
			stack = append(stack, node.Alias)
		}
	}
	return indexed
}

func fuzzNodeUnchangedFromSource(node *yaml.Node, indexed map[fuzzSourcePosition][]*yaml.Node) bool {
	if node == nil || node.Line <= 0 || node.Column <= 0 {
		return false
	}
	position := fuzzSourcePosition{kind: node.Kind, line: node.Line, column: node.Column}
	for _, source := range indexed[position] {
		if yamlNodeGraphEqual(node, source) {
			return true
		}
	}
	return false
}

// fuzzRetainedChildren applies only the documented safe duplicate cleanup.
// Non-string keys are never collapsed because they are not addressable by the
// package's mapping-path model.
func fuzzRetainedChildren(node *yaml.Node) []*yaml.Node {
	if node == nil || node.Kind != yaml.MappingNode {
		return nodeContent(node)
	}
	retained := make([]*yaml.Node, 0, len(node.Content))
	for index := 0; index+1 < len(node.Content); index += 2 {
		key := node.Content[index]
		shadowed := false
		if key != nil && key.Kind == yaml.ScalarNode && key.Tag == "!!str" {
			for later := index + 2; later+1 < len(node.Content); later += 2 {
				other := node.Content[later]
				if other != nil && other.Kind == yaml.ScalarNode && other.Tag == "!!str" && other.Value == key.Value {
					shadowed = true
					break
				}
			}
		}
		if !shadowed {
			retained = append(retained, key, node.Content[index+1])
		}
	}
	return retained
}

func nodeContent(node *yaml.Node) []*yaml.Node {
	if node == nil {
		return nil
	}
	return node.Content
}

// fuzzJSONDocument returns a JSON encoding suitable for an independent patch
// oracle. YAML duplicate keys do not have JSON object semantics, so they are
// deliberately excluded instead of being silently collapsed.
func fuzzJSONDocument(doc *yaml.Node) ([]byte, bool) {
	if doc == nil || doc.Kind != yaml.DocumentNode || len(doc.Content) != 1 || doc.Content[0] == nil ||
		fuzzHasDuplicateKeys(doc.Content[0], make(map[*yaml.Node]bool)) || yamlNodeHasNonJSONMetadata(doc.Content[0]) {
		return nil, false
	}
	encoded, err := json.Marshal(yamlNodeToInterface(doc.Content[0]))
	if err != nil {
		return nil, false
	}
	return encoded, true
}

// fuzzPatchOracleComparable independently classifies the RFC overlap shared
// by yamledit and evanphx/json-patch. It intentionally does not call
// decodePatchOps: otherwise a regression in the production decoder could
// disable the success/error parity assertion that this oracle is meant to
// provide.
func fuzzPatchOracleComparable(patchJSON []byte) bool {
	// encoding/json replaces malformed UTF-8 inside strings with U+FFFD, and
	// evanphx therefore accepts some byte sequences that yamledit deliberately
	// rejects before decoding. That stricter input-validation case is outside
	// the semantic overlap this oracle compares.
	if !utf8.Valid(patchJSON) {
		return false
	}
	validPointer := func(pointer string) bool {
		if pointer == "" {
			return true
		}
		if pointer[0] != '/' {
			return false
		}
		for _, token := range strings.Split(pointer[1:], "/") {
			if token == "" {
				// evanphx/json-patch treats an empty reference token as the
				// document root rather than an empty-string object member.
				return false
			}
		}
		for index := 0; index < len(pointer); index++ {
			if pointer[index] != '~' {
				continue
			}
			if index+1 >= len(pointer) || pointer[index+1] != '0' && pointer[index+1] != '1' {
				return false
			}
			index++
		}
		return true
	}
	decoder := json.NewDecoder(bytes.NewReader(patchJSON))
	first, err := decoder.Token()
	if err != nil {
		return false
	}
	array, ok := first.(json.Delim)
	if !ok || array != '[' {
		return false
	}
	for decoder.More() {
		first, err = decoder.Token()
		if err != nil {
			return false
		}
		object, ok := first.(json.Delim)
		if !ok || object != '{' {
			return false
		}
		members := make(map[string][]json.RawMessage)
		for decoder.More() {
			nameToken, err := decoder.Token()
			if err != nil {
				return false
			}
			name, ok := nameToken.(string)
			if !ok {
				return false
			}
			var raw json.RawMessage
			if err := decoder.Decode(&raw); err != nil {
				return false
			}
			members[name] = append(members[name], append(json.RawMessage(nil), raw...))
		}
		if _, err := decoder.Token(); err != nil {
			return false
		}

		if len(members["op"]) != 1 || len(members["path"]) != 1 {
			return false
		}
		var operation, path, from string
		opOK := json.Unmarshal(members["op"][0], &operation) == nil
		pathOK := json.Unmarshal(members["path"][0], &path) == nil
		if !opOK || !pathOK {
			return false
		}
		switch operation {
		case "add", "replace", "test":
			if len(members["value"]) != 1 {
				return false
			}
		case "move", "copy":
			if len(members["from"]) != 1 || json.Unmarshal(members["from"][0], &from) != nil {
				return false
			}
		case "remove":
		default:
			return false
		}
		if path == "" && operation != "test" {
			return false
		}
		if !validPointer(path) {
			return false
		}
		if operation == "move" && from == "" {
			return false
		}
		if (operation == "move" || operation == "copy") && !validPointer(from) {
			return false
		}
	}
	if _, err := decoder.Token(); err != nil {
		return false
	}
	var trailing any
	return decoder.Decode(&trailing) == io.EOF
}

// fuzzSourceMayNormalize mirrors the two documented no-op exceptions for
// parsed sources: duplicate mapping keys are collapsed with last-key-wins
// semantics, and implicit empty mapping values are materialized as {}. Even in
// these cases the caller still gets a semantic round-trip assertion above.
func fuzzSourceMayNormalize(source []byte) bool {
	var document yaml.Node
	if err := decodeSingleYAMLDocument(source, &document); err != nil || len(document.Content) != 1 || document.Content[0] == nil {
		return false
	}
	lineOffsets := buildLineOffsets(source)
	visiting := make(map[*yaml.Node]bool)
	var walk func(*yaml.Node) bool
	walk = func(node *yaml.Node) bool {
		if node == nil || visiting[node] {
			return false
		}
		visiting[node] = true
		defer delete(visiting, node)
		switch node.Kind {
		case yaml.DocumentNode, yaml.SequenceNode:
			for _, child := range node.Content {
				if walk(child) {
					return true
				}
			}
		case yaml.MappingNode:
			seen := make(map[string]struct{}, len(node.Content)/2)
			for i := 0; i+1 < len(node.Content); i += 2 {
				key, value := node.Content[i], node.Content[i+1]
				if key != nil && key.Kind == yaml.ScalarNode && key.Tag == "!!str" {
					if _, duplicate := seen[key.Value]; duplicate {
						return true
					}
					seen[key.Value] = struct{}{}
				}
				if (node.Tag == "" || node.Tag == "!!map") && key != nil && key.Kind == yaml.ScalarNode &&
					key.Tag == "!!str" && value != nil && value.Kind == yaml.ScalarNode &&
					value.Tag == "!!null" && value.Value == "" && value.Anchor == "" &&
					!scalarHasExplicitTag(source, lineOffsets, value) {
					return true
				}
				if walk(key) || walk(value) {
					return true
				}
			}
		case yaml.AliasNode:
			return walk(node.Alias)
		}
		return false
	}
	return walk(&document)
}

func fuzzContainsAlias(node *yaml.Node, visiting map[*yaml.Node]bool) bool {
	if node == nil || visiting[node] {
		return false
	}
	if node.Kind == yaml.AliasNode {
		return true
	}
	visiting[node] = true
	defer delete(visiting, node)
	for _, child := range node.Content {
		if fuzzContainsAlias(child, visiting) {
			return true
		}
	}
	return false
}

func fuzzHasDuplicateKeys(node *yaml.Node, visiting map[*yaml.Node]bool) bool {
	if node == nil || visiting[node] {
		return false
	}
	visiting[node] = true
	defer delete(visiting, node)

	switch node.Kind {
	case yaml.DocumentNode, yaml.SequenceNode:
		for _, child := range node.Content {
			if fuzzHasDuplicateKeys(child, visiting) {
				return true
			}
		}
	case yaml.MappingNode:
		seen := make(map[string]struct{}, len(node.Content)/2)
		for i := 0; i+1 < len(node.Content); i += 2 {
			key := node.Content[i]
			if key == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
				return true
			}
			if _, exists := seen[key.Value]; exists {
				return true
			}
			seen[key.Value] = struct{}{}
			if fuzzHasDuplicateKeys(node.Content[i+1], visiting) {
				return true
			}
		}
	case yaml.AliasNode:
		return fuzzHasDuplicateKeys(node.Alias, visiting)
	}
	return false
}
