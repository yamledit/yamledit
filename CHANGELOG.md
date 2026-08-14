# Release notes

## Unreleased — correctness and release hardening

This release establishes yamledit's intended API semantics and hardens its
source-preserving YAML edit engine. No release version has been selected yet.

### Value-setting semantics

`SetValue(mapNode, key, value, opts)` replaces the complete value at `key`.
`SetMapValues` is the explicit API for merging fields into an existing
mapping.

| Input to `SetValue` | Result |
| --- | --- |
| `map[string]any` | Replaces the complete mapping; unspecified fields are removed. |
| Empty `map[string]any{}` | Writes `{}`. |
| Empty `[]any{}` or `[]string{}` | Writes `[]`. |
| Direct `nil` | Deletes the target key. |
| Go floating-point value | Writes a YAML `!!float`, including integral values and negative zero. |
| Go integer or `uintptr` | Writes a YAML `!!int` at every nesting level. |
| Valid `json.Number` | Retains its JSON spelling and numeric category, using an explicit YAML tag when required. |
| Invalid `json.Number` | Writes a YAML string. |
| Unsupported Go type | Writes a quoted diagnostic marker. |

Replacing a custom-tagged scalar or collection with an ordinary Go value also
replaces its YAML tag. An existing anchor is retained so aliases continue to
refer to the replacement.

With `DeleteEmptyStrings`, empty string mapping fields are omitted recursively,
including mappings nested in sequences. Nil mapping fields are also omitted.
Empty strings and nil positional sequence elements remain values and are written
as an empty string and YAML null respectively. Use `SetScalarNull` for an
explicit null mapping field.

`SetValue` detects unsupported types and cyclic, excessively deep, or oversized
`map[string]any` and `[]any` graphs. Since the API has no error return, an
unrepresentable branch is written as a quoted `<yamledit: ...>` diagnostic
marker. Shared acyclic containers are expanded normally.

### Validation and safety

`Marshal` and JSON Patch validate public `yaml.Node` graphs before encoding or
mutation. Validation covers:

- exactly one mapping root in a `DocumentNode` where a complete document is
  required;
- paired, non-nil mapping entries and non-nil sequence children;
- acyclic `Content` edges, while recursive aliases through `Alias` edges remain
  valid;
- valid UTF-8 and representable node fields and styles; and
- aliases whose target is reachable, has the matching anchor name, and is the
  preceding anchor selected by the serialized alias name.

`Parse` accepts mapping keys represented directly by scalar nodes. Collection
and alias keys are rejected because the package path model cannot address them
safely. Typed scalar keys remain accepted.

Generated surgical and scoped-rewrite output is checked against the live YAML
values, scalar categories, and requested kind/tag changes. If no safe
representation is available, the edit returns an error instead of emitting a
partial or semantically different document.

For documents returned by `Parse`, `Marshal` detects direct changes to the
public AST, including values, kinds, tags, styles, comments, anchors, aliases,
and collection content. It globally encodes the live AST so those changes are
not silently ignored; this can reflow formatting outside the changed node.
Package-managed edits continue to use byte surgery or scoped rewrites when an
indexed source is available.

Callers must not read or mutate a returned `yaml.Node` concurrently with
yamledit API calls. Synchronization covers package API calls, not direct field
access.

### JSON Patch semantics

- Duplicate `op` or `path` members are rejected. Duplicate `value` is rejected
  for `add`, `replace`, and `test`; duplicate `from` is rejected for `move` and
  `copy`. Unknown members and members undefined for an operation are ignored.
- Copying the document root (`from: ""`) to a non-root destination is supported
  when the root is JSON-compatible.
- An operation that would detach an anchor still referenced elsewhere is
  rejected atomically. Replacing an anchored node preserves its identity so its
  aliases continue to resolve.
- Numeric `test` comparisons support arbitrarily large decimal exponents, and
  numeric additions and replacements preserve their JSON number category.
- Replacing a YAML-only or custom-tagged scalar with an ordinary JSON scalar
  removes the existing tag even when the lexical value is unchanged.
- The YAML document must retain a mapping root. Root `test` is supported, while
  root-target `add`, `remove`, `replace`, `move`, and `copy` are rejected. Moving
  from the root is also rejected.
- JSON Pointer paths do not traverse through aliases. Copying an alias
  materializes its resolved JSON-compatible value instead of creating another
  YAML alias.
- `move` rejects a source carrying YAML-only metadata such as a custom tag,
  anchor, alias, comment, or non-default scalar style, because JSON transfer
  cannot preserve it losslessly.
- A failed multi-operation patch leaves the live document unchanged.

### Correctness improvements

- Preserved requested scalar tags across same-lexeme replacements, composed
  mutations, sequence index shifts, and remove/reinsert histories.
- Preserved anchors and aliases when replacing anchored values, and rejected
  edits that would create dangling or ambiguously resolved aliases.
- Fixed multiline quoted, plain, block-scalar, flow-collection, tag-property,
  and CRLF source bounds.
- Indexed scalar tokens inside flow mappings so editing one member preserves
  shorthand nulls and the exact presentation of untouched siblings.
- Composed sequence-item scalar edits with appends while retaining untouched
  presentation and alias-valued fields.
- Preserved empty scalar identity, duplicate-item presentation, comments,
  nested collection types, and exact wide numeric values during sequence
  rewrites.
- Reconciled yaml.v3 and goccy parser projections when they accept an ambiguous
  flow spelling with different structures.
- Preserved mapping member order and retained JSON object presentation during
  complete replacements; genuinely new members append in requested order.
- Restored key and value comments in both the live AST and emitted YAML when a
  mapping key is removed and recreated.
- Preserved implicit YAML nulls exactly during no-op Parse/Marshal, including
  block and flow collections with comments, anchors, and noncanonical numeric
  spellings. Mapping conversion happens only when an edit explicitly requests it.
- Prevented duplicate inserted keys when logical and scalar-tag rewrite intents
  identify the same path.

### Engineering

- Added seeded fuzz targets for Parse/Marshal stability, JSON Patch atomicity
  and semantics, and bounded composed mutation histories.
- Added allocation-aware benchmarks for Parse, no-op Marshal, scalar surgery,
  structural and sequence edits, JSON Patch, and wide mapping/sequence
  presentation reconciliation.
- Replaced quadratic presentation matching for wide mapping and sequence
  replacements with indexed, collision-checked lookups.
- Added a GitHub Actions matrix for Go 1.24.1 and the current Go release on
  Linux, macOS, and Windows, plus race, vet, shuffled tests, fuzz smoke,
  formatting, changed-line whitespace checks, and benchmark smoke execution.
- Consolidated duplicate append and whole-sequence mapping renderers so both
  surgery paths share key ordering, duplicate collapse, scalar rendering, and
  indentation rules.
