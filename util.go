package yamledit

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math"
	"strconv"
	"strings"
	"unicode/utf8"

	gyaml "github.com/goccy/go-yaml"
	"gopkg.in/yaml.v3"
)

func cloneMapSlice(ms gyaml.MapSlice) gyaml.MapSlice {
	out := make(gyaml.MapSlice, 0, len(ms))
	for _, it := range ms {
		var v interface{}
		switch vv := it.Value.(type) {
		case gyaml.MapSlice:
			v = cloneMapSlice(vv)
		case []interface{}:
			v = cloneSlice(vv)
		default:
			v = vv
		}
		out = append(out, gyaml.MapItem{Key: it.Key, Value: v})
	}
	return out
}

func cloneSlice(in []interface{}) []interface{} {
	out := make([]interface{}, len(in))
	for i, e := range in {
		switch tv := e.(type) {
		case gyaml.MapSlice:
			out[i] = cloneMapSlice(tv)
		case []interface{}:
			out[i] = cloneSlice(tv)
		default:
			out[i] = tv
		}
	}
	return out
}

func validateOrderedUTF8(v interface{}) error {
	switch value := v.(type) {
	case string:
		if !utf8.ValidString(value) {
			return fmt.Errorf("yamledit: string value contains invalid UTF-8")
		}
	case gyaml.MapSlice:
		for _, item := range value {
			if key, ok := item.Key.(string); ok && !utf8.ValidString(key) {
				return fmt.Errorf("yamledit: mapping key contains invalid UTF-8")
			}
			if err := validateOrderedUTF8(item.Value); err != nil {
				return err
			}
		}
	case []interface{}:
		for _, item := range value {
			if err := validateOrderedUTF8(item); err != nil {
				return err
			}
		}
	case map[string]interface{}:
		for key, item := range value {
			if !utf8.ValidString(key) {
				return fmt.Errorf("yamledit: mapping key contains invalid UTF-8")
			}
			if err := validateOrderedUTF8(item); err != nil {
				return err
			}
		}
	}
	return nil
}

func normalizePatchLineEndings(original, generated []byte) []byte {
	firstLF := bytes.IndexByte(original, '\n')
	if firstLF <= 0 || original[firstLF-1] != '\r' || !bytes.Contains(generated, []byte{'\n'}) {
		return generated
	}
	out := make([]byte, 0, len(generated)+bytes.Count(generated, []byte{'\n'}))
	for i, b := range generated {
		if b == '\n' && (i == 0 || generated[i-1] != '\r') {
			out = append(out, '\r')
		}
		out = append(out, b)
	}
	return out
}

// yamlNodeHasNonJSONMetadata reports whether converting a YAML subtree through
// JSON would discard information. JSON Patch move currently transfers values
// through the package's ordered JSON view, so callers must reject such sources
// instead of silently dropping tags, anchors, aliases, comments, or style.
func yamlNodeHasNonJSONMetadata(root *yaml.Node) bool {
	seen := make(map[*yaml.Node]struct{})
	var walk func(*yaml.Node) bool
	walk = func(node *yaml.Node) bool {
		if node == nil {
			return false
		}
		if _, ok := seen[node]; ok {
			return false
		}
		seen[node] = struct{}{}

		styleCarriesMetadata := node.Style != 0
		if (node.Kind == yaml.MappingNode || node.Kind == yaml.SequenceNode) && node.Style&^yaml.FlowStyle == 0 {
			// Default-tag flow collections are ordinary JSON values. Their children
			// are checked independently for styles or metadata that would be lost.
			styleCarriesMetadata = false
		}
		if node.Kind == yaml.AliasNode || node.Anchor != "" || styleCarriesMetadata ||
			node.HeadComment != "" || node.LineComment != "" || node.FootComment != "" {
			return true
		}
		switch node.Kind {
		case yaml.ScalarNode:
			switch node.Tag {
			case "", "!!str", "!!null", "!!bool", "!!int", "!!float":
				// These scalar types have direct JSON equivalents.
			default:
				return true
			}
		case yaml.MappingNode:
			if node.Tag != "" && node.Tag != "!!map" {
				return true
			}
			for i := 0; i+1 < len(node.Content); i += 2 {
				key := node.Content[i]
				if key == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
					return true
				}
			}
		case yaml.SequenceNode:
			if node.Tag != "" && node.Tag != "!!seq" {
				return true
			}
		}

		for _, child := range node.Content {
			if walk(child) {
				return true
			}
		}
		return false
	}
	return walk(root)
}

func yamlNodeHasNonJSONType(root *yaml.Node) bool {
	visiting := make(map[*yaml.Node]bool)
	var walk func(*yaml.Node) bool
	walk = func(node *yaml.Node) bool {
		if node == nil {
			return false
		}
		if visiting[node] {
			return true
		}
		visiting[node] = true
		defer delete(visiting, node)
		if node.Kind == yaml.AliasNode {
			return walk(node.Alias)
		}
		switch node.Kind {
		case yaml.ScalarNode:
			switch node.Tag {
			case "", "!!str", "!!null", "!!bool", "!!int", "!!float":
			default:
				return true
			}
		case yaml.MappingNode:
			if node.Tag != "" && node.Tag != "!!map" {
				return true
			}
			for i := 0; i+1 < len(node.Content); i += 2 {
				if key := node.Content[i]; key == nil || key.Kind != yaml.ScalarNode || key.Tag != "!!str" {
					return true
				}
			}
		case yaml.SequenceNode:
			if node.Tag != "" && node.Tag != "!!seq" {
				return true
			}
		}
		for _, child := range node.Content {
			if walk(child) {
				return true
			}
		}
		return false
	}
	return walk(root)
}

// removalWouldBreakAlias detects aliases outside the removed subtree that
// point to the exact yaml.Node being removed. Comparing pointer identity is
// essential: YAML permits an anchor name to be reused, and syntax-only output
// validation would otherwise silently retarget the alias to another anchor.
func removalWouldBreakAlias(scanRoot *yaml.Node, targets ...*yaml.Node) bool {
	removed := make(map[*yaml.Node]struct{})
	var collect func(*yaml.Node)
	collect = func(node *yaml.Node) {
		if node == nil {
			return
		}
		if _, ok := removed[node]; ok {
			return
		}
		removed[node] = struct{}{}
		for _, child := range node.Content {
			collect(child)
		}
	}
	for _, target := range targets {
		collect(target)
	}

	seen := make(map[*yaml.Node]struct{})
	var walk func(*yaml.Node) bool
	walk = func(node *yaml.Node) bool {
		if node == nil {
			return false
		}
		if _, ok := seen[node]; ok {
			return false
		}
		seen[node] = struct{}{}
		_, insideRemoval := removed[node]
		if node.Kind == yaml.AliasNode && !insideRemoval && node.Alias != nil {
			if _, targetRemoved := removed[node.Alias]; targetRemoved {
				return true
			}
		}
		for _, child := range node.Content {
			if walk(child) {
				return true
			}
		}
		return false
	}
	return walk(scanRoot)
}

// validateYAMLAliasGraph verifies that every alias still points to the exact
// anchored node that remains reachable through the document's content tree.
func validateYAMLAliasGraph(root *yaml.Node) error {
	reachable := make(map[*yaml.Node]struct{})
	var collect func(*yaml.Node)
	collect = func(node *yaml.Node) {
		if node == nil {
			return
		}
		if _, ok := reachable[node]; ok {
			return
		}
		reachable[node] = struct{}{}
		for _, child := range node.Content {
			collect(child)
		}
	}
	collect(root)

	for node := range reachable {
		if node.Kind != yaml.AliasNode {
			continue
		}
		if node.Alias == nil {
			return fmt.Errorf("yamledit: invalid YAML alias %q has no target", node.Value)
		}
		if _, ok := reachable[node.Alias]; !ok {
			return fmt.Errorf("yamledit: invalid YAML alias %q refers to a removed anchor", node.Value)
		}
		if node.Alias.Anchor == "" || (node.Value != "" && node.Alias.Anchor != node.Value) {
			return fmt.Errorf("yamledit: invalid YAML alias %q no longer matches its anchor", node.Value)
		}
	}
	return nil
}

func cloneMapIndex(in map[string]*mapInfo) map[string]*mapInfo {
	out := make(map[string]*mapInfo, len(in))
	for k, v := range in {
		cp := *v
		out[k] = &cp
	}
	return out
}

func cloneValueIndex(in map[string][]valueOcc) map[string][]valueOcc {
	out := make(map[string][]valueOcc, len(in))
	for k, v := range in {
		cp := make([]valueOcc, len(v))
		copy(cp, v)
		out[k] = cp
	}
	return out
}

func keyEquals(k interface{}, want string) bool {
	switch vv := k.(type) {
	case string:
		return vv == want
	case fmt.Stringer:
		return vv.String() == want
	default:
		return false
	}
}

func isStringMappingKey(node *yaml.Node, want string) bool {
	return node != nil && node.Kind == yaml.ScalarNode && node.Tag == "!!str" && node.Value == want
}

func hasNonStringMappingKeyNamed(mapping *yaml.Node, want string) bool {
	if mapping == nil || mapping.Kind != yaml.MappingNode {
		return false
	}
	for i := 0; i+1 < len(mapping.Content); i += 2 {
		key := mapping.Content[i]
		if key != nil && key.Kind == yaml.ScalarNode && key.Value == want && key.Tag != "!!str" {
			return true
		}
	}
	return false
}

// Sentinel key used to index scalar values that are direct items of a sequence ("- <scalar>")
const scalarItemKey = "\x00s\x00"

func joinPath(path []string) string {
	if len(path) == 0 {
		return ""
	}
	var out strings.Builder
	for _, segment := range path {
		out.WriteString(strconv.Itoa(len(segment)))
		out.WriteByte(':')
		out.WriteString(segment)
	}
	return out.String()
}

func makePathKey(path []string, key string) string {
	return joinPath(append(append([]string{}, path...), key))
}

func clearDeletionMarkersAtOrBelow(st *docState, path []string) {
	if st == nil || len(st.toDelete) == 0 {
		return
	}
	for encoded := range st.toDelete {
		segments, ok := splitJoinedPath(encoded)
		if !ok || len(segments) < len(path) {
			continue
		}
		if pathSegmentsEqual(segments[:len(path)], path) {
			delete(st.toDelete, encoded)
		}
	}
}

func rebaseDeletionMarkersForSequence(st *docState, sequencePath []string, index, delta int, removeIndex bool) {
	if st == nil || len(st.toDelete) == 0 {
		return
	}
	updated := make(map[string]struct{}, len(st.toDelete))
	for encoded := range st.toDelete {
		segments, ok := splitJoinedPath(encoded)
		if !ok || len(segments) <= len(sequencePath) ||
			!pathSegmentsEqual(segments[:len(sequencePath)], sequencePath) {
			updated[encoded] = struct{}{}
			continue
		}
		itemSegment := segments[len(sequencePath)]
		if !isIndexPathSegment(itemSegment) {
			updated[encoded] = struct{}{}
			continue
		}
		itemIndex, err := strconv.Atoi(itemSegment[1 : len(itemSegment)-1])
		if err != nil {
			updated[encoded] = struct{}{}
			continue
		}
		if removeIndex && itemIndex == index {
			continue
		}
		if itemIndex > index || (!removeIndex && itemIndex >= index) {
			segments[len(sequencePath)] = indexSeg(itemIndex + delta)
			encoded = joinPath(segments)
		}
		updated[encoded] = struct{}{}
	}
	st.toDelete = updated
}

// makeSeqItemPathKey builds the length-prefixed internal key for a scalar item
// at a sequence index.
func makeSeqItemPathKey(path []string, idx int) string {
	segs := make([]string, 0, len(path)+1)
	segs = append(segs, path...)
	segs = append(segs, fmt.Sprintf("[%d]", idx))
	return joinPath(segs)
}

func splitJoinedPath(encoded string) ([]string, bool) {
	if encoded == "" {
		return nil, true
	}
	var out []string
	for pos := 0; pos < len(encoded); {
		colon := strings.IndexByte(encoded[pos:], ':')
		if colon < 0 {
			return nil, false
		}
		colon += pos
		length, err := strconv.Atoi(encoded[pos:colon])
		if err != nil || length < 0 || colon+1+length > len(encoded) {
			return nil, false
		}
		start := colon + 1
		out = append(out, encoded[start:start+length])
		pos = start + length
	}
	return out, true
}

func buildLineOffsets(b []byte) []int {
	offsets := []int{0}
	for i, c := range b {
		if c == '\n' {
			if i+1 < len(b) {
				offsets = append(offsets, i+1)
			}
		}
	}
	return offsets
}

func offsetFor(b []byte, lineOffsets []int, line, col int) int {
	// yaml.v3 uses 1-based line/column, and columns count Unicode code points
	// rather than bytes. Walk the line so non-ASCII keys do not shift a value's
	// byte offset into the middle of a UTF-8 sequence.
	if line <= 0 || col <= 0 || line > len(lineOffsets) {
		return -1
	}
	pos := lineOffsets[line-1]
	if line == 1 && pos == 0 && len(b) >= 3 && b[0] == 0xef && b[1] == 0xbb && b[2] == 0xbf {
		// yaml.v3 does not count a UTF-8 BOM as a source column.
		pos = 3
	}
	for currentCol := 1; currentCol < col; currentCol++ {
		if pos >= len(b) || b[pos] == '\n' {
			return -1
		}
		_, size := utf8.DecodeRune(b[pos:])
		if size == 0 {
			return -1
		}
		pos += size
	}
	return pos
}

// scalarValueOffset advances past YAML node properties such as anchors and
// explicit tags. yaml.v3 reports a scalar's Column at the first property, but
// surgery must replace only the value token or aliases will be left dangling.
func scalarValueOffset(b []byte, lineOffsets []int, node *yaml.Node) int {
	pos, _ := scalarValueProperties(b, lineOffsets, node)
	return pos
}

func scalarHasExplicitTag(b []byte, lineOffsets []int, node *yaml.Node) bool {
	_, hasTag := scalarValueProperties(b, lineOffsets, node)
	return hasTag
}

func scalarValueProperties(b []byte, lineOffsets []int, node *yaml.Node) (int, bool) {
	pos := offsetFor(b, lineOffsets, node.Line, node.Column)
	if pos < 0 || pos >= len(b) || node.Kind != yaml.ScalarNode {
		return pos, false
	}
	hasTag := false
	for {
		for pos < len(b) && (b[pos] == ' ' || b[pos] == '\t') {
			pos++
		}
		if pos >= len(b) || b[pos] == '\r' || b[pos] == '\n' || b[pos] == '#' {
			return -1, hasTag
		}
		if b[pos] != '&' && b[pos] != '!' {
			return pos, hasTag
		}
		if b[pos] == '!' {
			hasTag = true
			if pos+1 < len(b) && b[pos+1] == '<' {
				end := bytes.IndexByte(b[pos+2:], '>')
				if end < 0 {
					return -1, hasTag
				}
				pos += end + 3
				continue
			}
		}
		for pos < len(b) {
			c := b[pos]
			if c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '[' || c == ']' || c == '{' || c == '}' || c == ',' {
				break
			}
			pos++
		}
	}
}

func scalarYAMLTag(v interface{}) (string, bool) {
	switch value := v.(type) {
	case nil:
		return "!!null", true
	case bool:
		return "!!bool", true
	case int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64:
		return "!!int", true
	case float32, float64:
		return "!!float", true
	case json.Number:
		if strings.ContainsAny(string(value), ".eE") {
			return "!!float", true
		}
		return "!!int", true
	case string:
		return "!!str", true
	default:
		return "", false
	}
}

func lineStartOffset(lineOffsets []int, line int) int {
	if line <= 0 || line > len(lineOffsets) {
		return 0
	}
	return lineOffsets[line-1]
}

func findLineEnd(b []byte, from int) int {
	if from < 0 {
		return 0
	}
	for i := from; i < len(b); i++ {
		if b[i] == '\n' {
			return i
		}
	}
	// no newline; pretend the "end" sits at len-1 so 'end+1' is safe-checked by callers
	return len(b) - 1
}

// findScalarEndOnLine returns the end (exclusive) of the scalar token that starts at 'pos',
// scanning only within the current line. This is conservative and aims to handle:
//   - bare ints: -?[0-9_]+
//   - quoted scalars: '...' or "..." (we'll stop at the closing quote on this line)
//   - otherwise, we stop at the first '#' or end-of-line, trimming trailing spaces
func findScalarEndOnLine(b []byte, pos int) int {
	if pos < 0 || pos >= len(b) {
		return pos
	}
	i := pos
	// Determine line end (inclusive index: '\n' or len(b)-1)
	le := findLineEnd(b, pos)

	// Calculate exclusive end of line content (scanLimit).
	// If le points to '\n', scanLimit is le.
	// If le points to last char (EOF), scanLimit is le + 1 (len(b)).

	// Since pos < len(b), we know len(b) > 0 and le is a valid index.

	scanLimit := le
	// If the character at le is NOT '\n', it must be the EOF case (last char).
	if b[le] != '\n' {
		scanLimit = le + 1
	}

	// If quoted
	if b[i] == '\'' {
		i++ // after opening '
		// Use scanLimit (exclusive)
		for i < scanLimit {
			if b[i] == '\'' {
				// YAML single quotes escape as ''
				if i+1 < scanLimit && b[i+1] == '\'' {
					i += 2
					continue
				}
				return i + 1 // include closing quote
			}
			i++
		}
		return scanLimit // Unterminated quote ends at end of line.
	}
	if b[i] == '"' {
		i++ // after opening "
		esc := false
		for i < scanLimit {
			if esc {
				esc = false
				i++
				continue
			}
			if b[i] == '\\' {
				esc = true
				i++
				continue
			}
			if b[i] == '"' {
				return i + 1
			}
			i++
		}
		return scanLimit
	}

	// Bare token: read until comment or newline (scanLimit)
	j := pos
	for j < scanLimit {
		// In a plain YAML scalar, '#' starts a comment only at the beginning
		// or after whitespace. A fragment such as "url#anchor" is data.
		if b[j] == '#' && (j == pos || b[j-1] == ' ' || b[j-1] == '\t') {
			break
		}
		j++
	}
	// Trim trailing spaces before comment/hash
	k := j
	for k > pos && (b[k-1] == ' ' || b[k-1] == '\t' || b[k-1] == '\r') {
		k--
	}
	return k
}

// scalarSpansPhysicalLines reports scalars whose token or plain continuation
// extends beyond its first source line. Replacing only the first-line byte
// range would leave a closing quote or continuation text behind, so callers
// must promote these edits to a whole-entry structural rewrite.
func scalarSpansPhysicalLines(b []byte, node *yaml.Node, valStart, containerIndent int) bool {
	if node == nil || node.Kind != yaml.ScalarNode || valStart < 0 || valStart >= len(b) {
		return false
	}
	if node.Style&(yaml.LiteralStyle|yaml.FoldedStyle) != 0 {
		return true
	}
	if strings.Contains(node.Value, "\n") {
		return true
	}

	quote := b[valStart]
	if quote == '\'' || quote == '"' {
		spans := false
		escaped := false
		for i := valStart + 1; i < len(b); i++ {
			c := b[i]
			if c == '\n' {
				spans = true
			}
			if quote == '"' {
				if escaped {
					escaped = false
					continue
				}
				if c == '\\' {
					escaped = true
					continue
				}
				if c == '"' {
					return spans
				}
				continue
			}
			if c == '\'' {
				if i+1 < len(b) && b[i+1] == '\'' {
					i++
					continue
				}
				return spans
			}
		}
		// The parser accepted the node, so this is normally unreachable. Be
		// conservative if source/token accounting ever disagrees.
		return spans
	}

	firstEnd := findLineEnd(b, valStart)
	if firstEnd < 0 || firstEnd >= len(b)-1 || b[firstEnd] != '\n' {
		return false
	}
	for lineStart := firstEnd + 1; lineStart < len(b); {
		lineEnd := findLineEnd(b, lineStart)
		exclusive := lineEnd
		if lineEnd < len(b) && b[lineEnd] != '\n' {
			exclusive++
		}
		line := b[lineStart:exclusive]
		trimmed := bytes.TrimSpace(line)
		if len(trimmed) != 0 && trimmed[0] != '#' {
			return countLeadingIndent(line) > containerIndent
		}
		if lineEnd >= len(b)-1 || b[lineEnd] != '\n' {
			break
		}
		lineStart = lineEnd + 1
	}
	return false
}

// --------------------------------------------------------------------------------------
// Indent / sequence detection (unchanged)
// --------------------------------------------------------------------------------------

// detectIndentAndSequence returns the base indent, and whether sequences that are values
// of mapping keys are indented one level (true) or "indentless" (false).
func detectIndentAndSequence(b []byte) (int, bool) {
	indent := detectIndent(b)
	lines := bytes.Split(b, []byte("\n"))
	votes := 0 // >0 prefer indented seq, <0 prefer indentless

	for i := 0; i < len(lines); i++ {
		ln := lines[i]
		if isBlankOrComment(ln) {
			continue
		}
		if endsWithMappingKey(ln) {
			keyIndent := leadingSpaces(ln)
			// look ahead to the first non-blank, non-comment line
			for j := i + 1; j < len(lines); j++ {
				nxt := lines[j]
				if isBlankOrComment(nxt) {
					continue
				}
				lsp := leadingSpaces(nxt)
				trimmed := bytes.TrimLeft(nxt, " ")
				if len(trimmed) > 0 && trimmed[0] == '-' {
					if lsp == keyIndent+indent {
						votes++
					} else if lsp == keyIndent {
						votes--
					}
				}
				break
			}
		}
	}
	if votes > 0 {
		return indent, true
	}
	if votes < 0 {
		return indent, false
	}
	// default to indented sequences (common in K8s/Helm repos)
	return indent, true
}

func isBlankOrComment(ln []byte) bool {
	t := bytes.TrimSpace(ln)
	return len(t) == 0 || t[0] == '#'
}

// endsWithMappingKey returns true if the line is a block mapping key of the form "key:"
// possibly followed by spaces and/or a comment.
func endsWithMappingKey(ln []byte) bool {
	idx := bytes.IndexByte(ln, ':')
	if idx < 0 {
		return false
	}
	rest := bytes.TrimSpace(ln[idx+1:])
	return len(rest) == 0 || rest[0] == '#'
}

func detectIndent(b []byte) int {
	lines := bytes.Split(b, []byte("\n"))

	// Collect all non-zero indents from non-blank, non-comment lines
	indents := []int{}
	blockKeyIndent := -1
	for _, ln := range lines {
		if len(bytes.TrimSpace(ln)) == 0 {
			continue
		}
		// Skip pure comment lines
		trimmed := bytes.TrimLeft(ln, " ")
		if len(trimmed) > 0 && trimmed[0] == '#' {
			continue
		}

		n := leadingSpaces(ln)
		if blockKeyIndent >= 0 {
			if n > blockKeyIndent {
				continue
			}
			blockKeyIndent = -1
		}
		if n > 0 {
			indents = append(indents, n)
		}
		if lineStartsBlockScalar(ln) {
			blockKeyIndent = n
		}
	}

	if len(indents) == 0 {
		return 2
	}

	// Find the GCD of all indents to get base indent
	result := indents[0]
	for i := 1; i < len(indents); i++ {
		result = gcd(result, indents[i])
		if result == 1 {
			break // Can't get smaller than 1
		}
	}

	if result > 0 && result <= 8 {
		return result
	}
	return 2
}

func lineStartsBlockScalar(line []byte) bool {
	if comment := yamlCommentStart(line); comment >= 0 {
		line = line[:comment]
	}
	trimmed := bytes.TrimSpace(line)
	fields := bytes.Fields(trimmed)
	if len(fields) == 0 {
		return false
	}
	header := fields[len(fields)-1]
	if len(header) == 0 || (header[0] != '|' && header[0] != '>') {
		return false
	}
	for _, c := range header[1:] {
		if c != '+' && c != '-' && (c < '1' || c > '9') {
			return false
		}
	}
	return true
}

func gcd(a, b int) int {
	if a < 0 {
		a = -a
	}
	if b < 0 {
		b = -b
	}
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// makeSeqPathKey builds the index for a scalar key inside a mapping item located at a sequence under 'path'.
// The segment for the index is encoded as "[<idx>]" to avoid collisions with real keys.
func makeSeqPathKey(path []string, idx int, key string) string {
	segs := make([]string, 0, len(path)+2)
	segs = append(segs, path...)
	segs = append(segs, fmt.Sprintf("[%d]", idx))
	segs = append(segs, key)
	return joinPath(segs)
}

func leadingSpaces(line []byte) int {
	i := 0
	for i < len(line) && line[i] == ' ' {
		i++
	}
	return i
}

func firstNonSpaceByte(line []byte) byte {
	for _, b := range line {
		if b != ' ' && b != '\t' {
			return b
		}
	}
	return 0
}

// --------------------------------------------------------------------------------------
// Fallback helpers: shape-change detection + dedupe
// --------------------------------------------------------------------------------------

func hasShapeChange(originalOrdered, current gyaml.MapSlice) bool {
	om := lastMap(originalOrdered)
	cm := lastMap(current)
	for k, ov := range om {
		cv, ok := cm[k]
		if !ok {
			// key was removed entirely; we don't treat that as a shape change here
			// because DeleteKey is handled surgically via boundsByPathKey.
			continue
		}

		// Mapping vs non-mapping transitions (scalar -> map, map -> scalar)
		if oMap, okMap := ov.(gyaml.MapSlice); okMap {
			cMap, cOk := cv.(gyaml.MapSlice)
			if !cOk {
				return true
			}
			if len(oMap) > 0 && len(cMap) > 0 {
				if hasShapeChange(oMap, cMap) {
					return true
				}
			}
			continue
		} else if _, cIsMap := cv.(gyaml.MapSlice); cIsMap {
			// scalar/sequence -> map
			return true
		}

		// Sequence transitions
		oSlice, oIsSlice := ov.([]interface{})
		cSlice, cIsSlice := cv.([]interface{})
		if oIsSlice && cIsSlice {
			// We treat "non-empty -> empty" as a structural change; this is
			// what drives fallback for cases like deleting all array items and
			// wanting "externalSecretEnvs: []".
			if len(oSlice) > 0 && len(cSlice) == 0 {
				return true
			}
			continue
		}
		if oIsSlice != cIsSlice {
			return true
		}
	}
	return false
}

func lastMap(ms gyaml.MapSlice) map[string]interface{} {
	m := make(map[string]interface{}, len(ms))
	for _, it := range ms {
		if k, ok := it.Key.(string); ok {
			m[k] = it.Value
		}
	}
	return m
}

// --------------------------------------------------------------------------------------
// string token helpers for surgical replacements/insertions
// --------------------------------------------------------------------------------------

var yamlBareDisallowed = map[string]struct{}{
	"true": {}, "false": {}, "True": {}, "False": {},
	"yes": {}, "no": {}, "Yes": {}, "No": {},
	"on": {}, "off": {}, "On": {}, "Off": {},
	"null": {}, "Null": {}, "NULL": {}, "~": {},
}

// isScalarValue reports whether v is a "simple" scalar that we can safely render
// with renderScalar (i.e. not a nested list/map).
func isScalarValue(v interface{}) bool {
	switch v.(type) {
	case int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64, float32, float64, json.Number, bool, string, nil:
		return true
	default:
		return false
	}
}

func renderScalarToken(v interface{}) (string, bool) {
	switch value := v.(type) {
	case nil:
		return "null", true
	case bool:
		return strconv.FormatBool(value), true
	case int:
		return strconv.Itoa(value), true
	case int8:
		return strconv.FormatInt(int64(value), 10), true
	case int16:
		return strconv.FormatInt(int64(value), 10), true
	case int32:
		return strconv.FormatInt(int64(value), 10), true
	case int64:
		return strconv.FormatInt(value, 10), true
	case uint:
		return strconv.FormatUint(uint64(value), 10), true
	case uint8:
		return strconv.FormatUint(uint64(value), 10), true
	case uint16:
		return strconv.FormatUint(uint64(value), 10), true
	case uint32:
		return strconv.FormatUint(uint64(value), 10), true
	case uint64:
		return strconv.FormatUint(value, 10), true
	case float32:
		return formatYAMLFloat(float64(value)), true
	case float64:
		return formatYAMLFloat(value), true
	case json.Number:
		return string(value), true
	case string:
		return renderStringToken(value), true
	default:
		return "", false
	}
}

func isSafeBareString(s string) bool {
	if _, bad := yamlBareDisallowed[s]; bad {
		return false
	}
	if len(s) == 0 {
		return false
	}
	// Disallow whitespace or YAML special chars that frequently need quoting
	for _, r := range s {
		switch r {
		case ' ', '\t', '\n', ':', '#', '{', '}', '[', ']', ',', '&', '*', '!', '|', '>', '\'', '"', '%', '@', '`':
			return false
		}
	}

	// Syntax alone is not enough: values such as 123, true, .nan, and dates
	// are valid plain YAML but resolve to non-string tags. Ask yaml.v3 how the
	// candidate resolves and only emit it bare when it remains the exact string.
	var doc yaml.Node
	if err := yaml.Unmarshal([]byte("value: "+s+"\n"), &doc); err != nil || len(doc.Content) == 0 {
		return false
	}
	root := doc.Content[0]
	if root.Kind != yaml.MappingNode || len(root.Content) < 2 {
		return false
	}
	v := root.Content[1]
	return v.Kind == yaml.ScalarNode && v.Tag == "!!str" && v.Value == s
}

func hasYAMLControlCharacters(s string) bool {
	if !utf8.ValidString(s) {
		return true
	}
	for _, r := range s {
		// YAML's printable set excludes C0/C1 controls and Unicode
		// noncharacters. U+FEFF is technically printable away from the start of
		// a stream, but escaping it avoids it being mistaken for an embedded BOM
		// by less careful readers. The Unicode line/paragraph separators must also
		// be escaped because YAML treats them as physical line breaks.
		if r < 0x20 || (r >= 0x7f && r <= 0x9f) || r == 0x2028 || r == 0x2029 || r == 0xfeff ||
			(r >= 0xfdd0 && r <= 0xfdef) || r&0xffff == 0xfffe || r&0xffff == 0xffff {
			return true
		}
	}
	return false
}

func renderStringToken(s string) string {
	if isSafeBareString(s) {
		return s
	}
	return quoteNewStringToken(s)
}

func renderMappingKey(key string) string {
	return renderStringToken(key)
}

func formatYAMLFloat(v float64) string {
	switch {
	case math.IsNaN(v):
		return ".nan"
	case math.IsInf(v, 1):
		return ".inf"
	case math.IsInf(v, -1):
		return "-.inf"
	}

	s := strconv.FormatFloat(v, 'g', -1, 64)
	if !strings.ContainsAny(s, ".eE") {
		s += ".0"
	}
	return s
}

// Use existing quote style when replacing; if old token was bare but new is unsafe, add quotes.
func stringReplacementToken(oldTok []byte, newVal string) []byte {
	if len(oldTok) > 0 && oldTok[0] == '\'' && !hasYAMLControlCharacters(newVal) {
		// single-quoted → escape by doubling single quotes
		return []byte("'" + strings.ReplaceAll(newVal, "'", "''") + "'")
	}
	if len(oldTok) > 0 && oldTok[0] == '"' {
		return []byte(`"` + escapeDoubleQuotes(newVal) + `"`)
	}
	// If the original token was bare and the value didn't change, keep it as-is.
	if string(oldTok) == newVal {
		return append([]byte(nil), oldTok...)
	}
	// Bare previously
	if isSafeBareString(newVal) {
		return []byte(newVal)
	}
	// default to double-quoted for safety
	return []byte(`"` + escapeDoubleQuotes(newVal) + `"`)
}

// For new insertions, prefer single quotes (no escapes) if possible; otherwise double-quote.
func quoteNewStringToken(s string) string {
	if !strings.Contains(s, "'") && !hasYAMLControlCharacters(s) {
		return "'" + s + "'"
	}
	return quoteYAMLDoubleString(s)
}

func escapeDoubleQuotes(s string) string {
	quoted := quoteYAMLDoubleString(s)
	return quoted[1 : len(quoted)-1]
}

func quoteYAMLDoubleString(s string) string {
	quoted := strconv.Quote(s)
	if hasYAMLControlCharacters(s) {
		// QuoteToASCII guarantees that forbidden/noncharacter runes and invalid
		// UTF-8 bytes never leak into the YAML byte stream. YAML accepts the Go
		// \x/\u/\U escape forms used here in double-quoted scalars.
		quoted = strconv.QuoteToASCII(s)
	}
	// YAML treats these Unicode code points as line breaks even inside
	// single-quoted scalars. Escape them explicitly so the exact string survives.
	quoted = strings.ReplaceAll(quoted, "\u0085", `\u0085`)
	quoted = strings.ReplaceAll(quoted, "\u2028", `\u2028`)
	quoted = strings.ReplaceAll(quoted, "\u2029", `\u2029`)
	return quoted
}

// --------------------------------------------------------------------------------------
// maxLineEndForNode returns the maximum line-end offset (index of '\n' or len-1)
// for the given node and all of its descendants, based on yaml.v3 position info.
func maxLineEndForNode(st *docState, n *yaml.Node) int {
	if n == nil {
		return 0
	}
	maxEnd := 0
	var walk func(*yaml.Node)
	walk = func(n *yaml.Node) {
		if n == nil {
			return
		}
		if n.Line > 0 && n.Column > 0 {
			vs := scalarValueOffset(st.original, st.lineOffsets, n)
			if vs >= 0 && vs < len(st.original) {
				le := findLineEnd(st.original, vs)
				if n.Kind == yaml.ScalarNode && (st.original[vs] == '|' || st.original[vs] == '>') {
					lineStart := lineStartOffset(st.lineOffsets, n.Line)
					lineEnd := findLineEnd(st.original, lineStart)
					keyIndent := leadingSpaces(st.original[lineStart:min(lineEnd+1, len(st.original))])
					le = extendScalarBlockEnd(st.original, st.lineOffsets, n.Line, keyIndent)
				}
				if le > maxEnd {
					maxEnd = le
				}
			}
		}
		for _, c := range n.Content {
			walk(c)
		}
	}
	walk(n)
	return maxEnd
}

// extendScalarBlockEnd walks forward from the scalar's line and includes
// any following lines that are part of the same scalar block.
// A continuation line is blank, or more-indented than the key's indent.
func extendScalarBlockEnd(b []byte, lineOffsets []int, scalarLine int, keyIndent int) int {
	lastEnd := findLineEnd(b, lineStartOffset(lineOffsets, scalarLine))

	for li := scalarLine + 1; li <= len(lineOffsets); li++ {
		start := lineStartOffset(lineOffsets, li)
		if start >= len(b) {
			break
		}
		end := findLineEnd(b, start)
		line := b[start:end]
		trimmed := bytes.TrimSpace(line)
		if len(trimmed) == 0 {
			// blank line → still part of block
			lastEnd = end
			continue
		}
		indent := leadingSpaces(line)
		if indent > keyIndent {
			// more-indented than key → still part of this scalar block
			lastEnd = end
			continue
		}
		// indentation <= keyIndent → new sibling key / mapping
		break
	}
	return lastEnd
}
