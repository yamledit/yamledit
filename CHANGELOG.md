# Changelog

## Unreleased — correctness and release hardening

This entry covers the correctness changes introduced by `0c9ad45` relative to
`3919c17`, plus the follow-on release hardening tracked in
`RELEASE_TRACKING.md`. No release version has been selected.

### Compatibility and semantic-version recommendation

The exported Go function and type signatures are unchanged, so existing callers
remain source-compatible. The release nevertheless contains intentional changes
to ordinary `SetValue` results. In particular, maps are now replacements rather
than merges, and empty collections are retained instead of deleting or retaining
an old value.

Treat this as a **major-level compatibility change** if the existing behavior is
already public. This is a compatibility recommendation, not a version assignment;
the repository currently has no conventional semantic-version release tags.

### Breaking behavior changes

#### `SetValue` now has consistent replacement semantics

`SetValue(mapNode, key, value, opts)` now replaces the complete value at `key`.

| Input | Before `0c9ad45` | After `0c9ad45` |
| --- | --- | --- |
| `map[string]any` | Merged fields into the existing mapping. Unspecified fields remained. | Replaces the mapping. Unspecified fields are removed. |
| Empty `map[string]any{}` | Could leave an existing mapping unchanged. | Writes `{}`. |
| Empty `[]any{}` or `[]string{}` | Deleted the key. | Writes `[]`. |
| Integral `float64` | Could be emitted as `!!int`. | Remains `!!float`, for example `4.0`. |
| Fixed-width integers and `int`/`uint`/`uintptr` | Some direct values fell back to strings. | Emit as `!!int` at every nesting level. |
| Valid `json.Number` | Direct values could fall back to strings; very large values could lose their category. | Retains its JSON spelling and integer/float category, using an explicit YAML tag when needed. |
| Invalid `json.Number` | Could be treated as trusted scalar syntax in a nested value. | Is emitted as a YAML string. |

`nil` passed directly to `SetValue` still deletes the target key.
Replacing an existing custom-tagged scalar or collection with an ordinary Go
value also replaces its YAML tag with the ordinary requested tag. An existing
anchor is retained so external aliases keep referring to the replacement.

Migration guidance:

- Keep using `SetValue` when complete replacement is intended.
- To retain the old map-merge behavior, obtain the child mapping and call
  `SetMapValues`:

  ```go
  child := yamledit.EnsurePath(parent, "config")
  yamledit.SetMapValues(child, updates, opts)
  ```

- Use `DeleteKey` or `SetValue(..., nil, ...)` to delete a collection. Do not use
  an empty slice as a deletion signal.
- Pass a Go integer type for YAML integers, a Go float type for YAML floats, and a
  string when textual representation is intended. Code that compares YAML tags
  should account for this stricter type preservation.

#### Recursive omission rules are now uniform

With `DeleteEmptyStrings`, empty string **mapping fields** are omitted recursively,
including mappings nested in sequences. `nil` mapping fields are also omitted.
Empty strings and `nil` used as positional sequence elements remain values and are
written as an empty string and YAML null respectively.

To write an explicit null mapping field, address that mapping and call
`SetScalarNull`; do not place `nil` in a `map[string]any` replacement.

#### Caller collection graphs are bounded

`SetValue` now detects cyclic, excessively deep, and oversized `map[string]any` /
`[]any` graphs. Because the API has no error return, an unrepresentable branch is
written as a quoted `<yamledit: ...>` diagnostic marker instead of recursing until
a stack overflow. Shared acyclic containers are expanded normally.

Treat these inputs as unsupported data rather than depending on the marker text.
Validate or flatten caller data before calling `SetValue` when a marker would be
unacceptable.

### Stricter validation and error behavior

`Marshal` and JSON Patch now reject malformed public `yaml.Node` graphs before
encoding or mutation. Validation covers:

- exactly one mapping root in a `DocumentNode` where a complete document is
  required;
- paired, non-nil mapping entries and non-nil sequence children;
- acyclic `Content` edges (recursive aliases through `Alias` edges remain valid);
- valid UTF-8 and node fields/styles that the YAML encoder can represent; and
- aliases whose pointer target is reachable, has a matching anchor name, and is
  the preceding anchor that the serialized alias name would select.

`Parse` now requires each mapping key to be represented directly by a scalar
node. Collection-valued (complex) keys and alias keys are rejected because they
cannot be addressed safely by the package path model. Scalar nodes, including
typed scalar nodes, remain accepted.

Generated surgical and scoped-rewrite output is also checked against the live
YAML values, scalar categories, and requested kind/tag changes. A case that could
previously panic, silently omit data, retain the wrong tag, or return an incomplete
edit now returns an error when no safe representation is available.

Migration guidance:

- Always check errors from `Marshal` and the JSON Patch entry points.
- Construct complete documents as a `DocumentNode` containing exactly one
  `MappingNode`. Do not use nil children, unmatched mapping keys, conflicting
  styles, or cycles in `Content`.
- Model recursion with a valid anchored node plus `AliasNode`, not a `Content`
  cycle. Keep alias names consistent with their targets; unique anchor names are
  the least surprising choice.
- If an edit now returns “surgical edit unsupported,” narrow the edit to a scalar,
  mapping member, or sequence index whose source extent can be preserved.

### Direct `yaml.Node` mutation

For documents returned by `Parse`, `Marshal` now detects direct changes to the
public AST, including values, kinds, tags, styles, comments, anchors, aliases, and
collection content. It globally encodes the live AST so such changes are not
silently ignored. This can reflow formatting outside the changed node.

On an indexed, nonempty source, package-managed edits still use byte surgery or
scoped rewrites and do not fall back to a global re-encode when unsafe. A new or
trivia-only document has no source regions to preserve and is encoded normally.

Migration guidance:

- Prefer `EnsurePath`, setters, `DeleteKey`, and JSON Patch when byte stability is
  required.
- If direct AST mutation is necessary, expect encoder formatting rather than a
  minimal textual diff, and handle a validation error for an unrepresentable AST.
- Do not access or mutate the returned `yaml.Node` concurrently with yamledit API
  calls. Synchronization covers calls through package APIs on documents returned
  by `Parse`, not raw field access.

### JSON Patch compatibility

Changed behavior:

- Duplicate `op` or `path` members are rejected. Duplicate `value` is rejected
  for `add`, `replace`, and `test`; duplicate `from` is rejected for `move` and
  `copy`. Unknown members and members undefined for the selected operation remain
  ignored.
- Copying the current document root (`from: ""`) to a non-root destination is now
  supported when the root is JSON-compatible.
- An operation that would detach an anchor still referenced elsewhere is rejected
  atomically. Replacing the anchored node itself preserves its identity so its
  aliases continue to resolve.
- Numeric `test` comparisons support arbitrarily large decimal exponents, and
  numeric additions/replacements preserve their JSON number category.
- Replacing a YAML-only/custom-tagged scalar with an ordinary JSON scalar now
  removes the old tag even when the lexical value is unchanged.

Intentional RFC 6902 constraints in yamledit:

- The edited YAML document must retain a mapping root. Root `test` is supported,
  but root-target `add`, `remove`, `replace`, `move`, and `copy` are rejected.
  Moving from the root is also rejected.
- Copying from the root to a non-root path is supported, but the source must be
  JSON-compatible.
- JSON Pointer paths do not traverse through a YAML alias. Copying an alias
  materializes its resolved JSON-compatible value rather than creating a new YAML
  alias.
- `move` rejects a source carrying YAML-only metadata—such as a custom tag,
  anchor, alias, comment, or non-default scalar style—because JSON transfer cannot
  preserve it losslessly.
- A failed multi-operation patch leaves the live document unchanged.

### Correctness fixes

- Preserved requested scalar tags across same-lexeme replacements, sequential
  mutations, sequence index shifts, and remove/reinsert histories.
- Preserved anchors and external aliases when replacing an anchored value, and
  rejected edits that would create dangling or ambiguously resolved aliases.
- Fixed multiline quoted, plain, block-scalar, flow-collection, tag-property, and
  CRLF source bounds so scoped edits do not leave continuation bytes behind.
- Composed sequence-item scalar edits with appends while retaining untouched
  presentation and alias-valued fields.
- Preserved empty scalar identity, duplicate-item presentation, comments, nested
  collection types, and exact wide numeric values during sequence rewrites.
- Made same-lexeme tag replacements stable across repeated `Marshal` calls and
  prevented parser representation differences from triggering a false
  direct-AST rewrite on no-op documents.
- Kept implicit-empty-map normalization from overwriting the winning value in a
  duplicate-key mapping, including nested shadowed mappings.
- Reconciled the internal ordered shadow with the returned yaml.v3 AST when the
  two YAML parsers accept an ambiguous flow spelling with different structures.
- Kept an existing parent mapping member in place during `SetValue` and JSON
  Patch replacement. Retained JSON object members preserve their source order
  and presentation, while genuinely new members are appended; complete
  `SetValue` collection replacements still honor the caller's requested order.
- Treated a removed then recreated mapping key as a new appended member while
  restoring its original key/value comments in both the live AST and emitted
  YAML. Reinsertion ordering now survives transient sequence-index shifts.
- Kept scalar-to-collection inline comments on the mapping key without leaving
  a duplicate comment on the installed live value, and tightened plain-scalar
  comment recognition so quote characters inside tokens do not hide comments.
- Preserved parser-recognized comments, anchors, and untouched numeric spellings
  when implicit empty maps inside flow collections require a scoped rewrite;
  normalization now fails closed around a bare non-specific `!` tag that the
  encoder cannot reproduce faithfully.
- Prevented a newly inserted key from being emitted twice when a later edit adds
  both a logical change and a scalar-tag rewrite intent for the same path.

### Release engineering

- Added seeded fuzz targets for Parse/Marshal stability, JSON Patch atomicity and
  semantics, and bounded composed mutation histories. Initial fuzzing found
  several of the follow-on correctness issues listed above.
- Added allocation-aware small and large benchmarks for Parse, no-op Marshal,
  scalar surgery, structural and sequence edits, multi-operation JSON Patch,
  and wide mapping/sequence presentation reconciliation.
- Replaced quadratic presentation matching for wide JSON Patch mapping and
  sequence replacements with indexed, collision-checked lookups while retaining
  last-wins duplicate and ambiguous-identity safeguards.
- Added a GitHub Actions matrix for the minimum and current Go toolchains on
  Linux, macOS, and Windows, plus race, vet, shuffled tests, fuzz smoke tests,
  formatting, changed-line whitespace checks, and benchmark smoke execution.
- Consolidated duplicate append/whole-sequence mapping renderers so both surgery
  paths share key ordering, duplicate collapse, scalar rendering, and indentation
  rules.

### Upgrade checklist

1. Search for `SetValue` calls whose value is `map[string]any`; decide explicitly
   between replacement (`SetValue`) and merge (`EnsurePath` + `SetMapValues`).
2. Search for empty slices formerly used to delete keys and replace them with
   `DeleteKey` or direct `nil`.
3. Review code that depends on YAML numeric tags or on integral floats becoming
   integers.
4. Review `DeleteEmptyStrings` use in nested maps and explicit-null requirements.
5. Ensure every `Marshal` and JSON Patch error is handled.
6. Remove malformed or concurrently mutated raw AST construction, or accept the
   global re-encode semantics for valid direct AST edits.
7. Review JSON Patch documents for duplicate defined members and root-target
   operations.
