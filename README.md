# yamledit

![](./images/banner.png)

A Go package for **surgical YAML edits** that preserves comments, formatting, key order, and minimizes diffs.
Think: *change exactly the bytes you mean to - leave everything else untouched.*

- **Zero‑churn scalars.** Update ints/strings/bools/floats/null in place, keeping quote style, spaces, and inline
  comments.
- **Append without reflow.** Insert new keys/items at the _right_ indent and position.
- **JSON Patch built‑in.** Apply RFC‑6902 patches (optionally at a base path) with minimal diffs when safe.
- **Thread‑safe APIs.** Concurrent calls through yamledit’s mutators and `Marshal` are synchronized for documents
  returned by `Parse`.

> **Why not parse & re‑encode?** Re‑encoding churns quotes, spaces, and comment whitespace. `yamledit` indexes exact
> byte positions so unrelated lines are **byte‑for‑byte identical**.

---

## Installation

```bash
go get github.com/yamledit/yamledit
```

Go 1.24.1+

---

## Quick start

```go
package main

import (
	"fmt"
	"os"

	"github.com/yamledit/yamledit"
	"gopkg.in/yaml.v3"
)

func main() {
	// 1) Read and parse (top-level must be a mapping; empty is okay)
	data, _ := os.ReadFile("config.yaml")
	doc, err := yamledit.Parse(data)
	if err != nil {
		panic(err)
	}

	// 2) Navigate/create nested mappings
	env := yamledit.EnsurePath(doc, "service", "env")

	// 3) Surgical scalar updates (quotes & inline comments on other lines preserved)
	yamledit.SetScalarInt(env, "PORT", 9090)
	yamledit.SetScalarBool(env, "METRICS_ENABLED", true)
	yamledit.SetScalarString(env, "GREETING", "hi") // keeps prior quote style if it existed
	yamledit.SetScalarNull(env, "OPTIONAL_VALUE")   // !!null

	// 4) Delete keys surgically (removes full blocks, including arrays)
	yamledit.DeleteKey(env, "OLD_FLAG")

	// 5) Marshal back (surgery when safe; scoped rewrite when needed)
	out, err := yamledit.Marshal(doc)
	if err != nil {
		panic(err)
	}

	if err := os.WriteFile("config.yaml", out, 0o644); err != nil {
		panic(err)
	}
	fmt.Println("Updated config.yaml")
	_ = yaml.Node{} // just to show the import, not required further
}
```

**No quote churn example**

Input:

```yaml
env:
  HTTP_CORS_ALLOWED_ORIGINS: '*'
  METRICS_ENABLED: "true"
  port: 8080
```

Code:

```go
svc := yamledit.EnsurePath(doc, "env")
yamledit.SetScalarInt(svc, "port", 9090)
out, _ := yamledit.Marshal(doc)
```

Output (only one line changed; quotes preserved):

```yaml
env:
  HTTP_CORS_ALLOWED_ORIGINS: '*'
  METRICS_ENABLED: "true"
  port: 9090
```

---

## API overview

> All functions are in `github.com/yamledit/yamledit`.

### Core

* `Parse(data []byte) (*yaml.Node, error)`
  Parse bytes into a `yaml.Node`. Top‑level **must** be a mapping (empty input creates an empty mapping document).
  Every mapping key must be represented directly by a YAML scalar node; collection and alias keys are rejected because
  the package's path/index model cannot address them safely.

* `Marshal(doc *yaml.Node) ([]byte, error)`
  Serialize back to bytes. Edits made through this package use byte surgery or a scoped per-key/sequence rewrite; if
  neither is safe, `Marshal` returns an error instead of reformatting the whole source. If you mutate fields on the
  returned `yaml.Node` directly, `Marshal` encodes that live AST globally so it does not silently ignore the change;
  direct AST edits may therefore reflow formatting outside the changed node.

* `EnsurePath(node *yaml.Node, first string, rest ...string) *yaml.Node`
  Navigate/create nested mappings, starting from a `DocumentNode` **or** an inner `MappingNode`. Returns the mapping
  node at that path.

### Scalar setters (surgical updates)

* `SetScalarInt(mapNode *yaml.Node, key string, value int)`
* `SetScalarString(mapNode *yaml.Node, key, value string)`
* `SetScalarBool(mapNode *yaml.Node, key string, value bool)` → **canonicalizes to bare** `true`/`false`
* `SetScalarFloat(mapNode *yaml.Node, key string, value float64)`
* `SetScalarNull(mapNode *yaml.Node, key string)` → `!!null`

> Behavior: If the key exists, we replace only the value token (preserving spacing and inline comment).
> If it’s new, it’s appended at the mapping’s indent; strings are safely quoted on insertion.

### Generic value setters

* `SetValue(mapNode *yaml.Node, key string, value any, opts SetValueOptions)`
  Replaces the value under a mapping key with a scalar, mapping, or sequence. Signed and unsigned Go integers are
  written as YAML integers; `float32`/`float64` remain YAML floats even when integral; valid `json.Number` values retain
  their numeric category and spelling. Empty slices and maps are written as `[]` and `{}`. A `nil` value deletes the
  key. A `map[string]any` is a complete replacement; use `SetMapValues` when you want to merge individual fields into
  an existing mapping. Unsupported types and cyclic, excessively deep, or oversized caller collections are bounded;
  because this setter has no error return, an unrepresentable branch is emitted as a quoted diagnostic string.

* `SetMapValues(mapNode *yaml.Node, fields map[string]any, opts SetValueOptions)`
  Writes multiple `SetValue`-supported values into a mapping node.

* `SetStringMapValues(mapNode *yaml.Node, fields map[string]string, opts SetValueOptions)`
  Writes multiple string values into a mapping node.

* `SetValueOptions{DeleteEmptyStrings bool, SortKeys bool}`
  Controls whether empty string mapping fields are omitted/deleted and whether map keys are written in lexical order.
  Empty strings used as positional sequence elements are retained.

Example:

```go
spec := yamledit.EnsurePath(doc, "spec")
yamledit.SetMapValues(spec, map[string]any{
	"enabled": true,
	"ports":   []string{"http", "grpc"},
	"selector": map[string]any{
		"app": "checkout",
	},
}, yamledit.SetValueOptions{SortKeys: true})
```

### Deletion (surgical)

* `DeleteKey(mapNode *yaml.Node, key string)`
  Removes **all occurrences** of the key under that mapping. Deletion uses pre‑indexed start/end byte boundaries to
  remove the entire block (scalars, mappings, or arrays). If neither exact deletion nor a safe scoped rewrite is
  possible, `Marshal` returns an error rather than reformatting unrelated lines.

### JSON Patch (RFC‑6902)

* `ApplyJSONPatchBytes(node *yaml.Node, patchJSON []byte) error`
* `ApplyJSONPatch(node *yaml.Node, patch jsonpatch.Patch) error`
* `ApplyJSONPatchAtPathBytes(node *yaml.Node, patchJSON []byte, basePath []string) error`
* `ApplyJSONPatchAtPath(node *yaml.Node, patch jsonpatch.Patch, basePath []string) error`

**Notes**

* `basePath` lets you interpret each op’s pointer **relative** to a mapping path (e.g. `[]string{"service","envs"}`).
* Arrays: targeted edits (`/0/property`, `/-` appends) often remain **surgical**. Whole‑array replaces may fall back.
* Root-target mutations (`path: ""`) are rejected because edited documents must keep a mapping root; root `test` is supported.
* Copying from the root (`from: ""`) to a non-root path is supported; moving from the root is rejected.
* An alias value can be tested or copied, but paths do not traverse through an alias into its target mapping. Copy
  materializes the alias’s resolved JSON-compatible value; it does not create another YAML alias.
* YAML-only values or presentation metadata can make an operation unsupported. For example, `move` rejects a source
  carrying a custom tag, anchor, alias, comment, or non-default scalar style instead of silently discarding it.

**Example: replace a field inside an array item (single‑line diff)**

```go
patch := []byte(`[{"op":"replace","path":"/0/property","value":"target-new"}]`)
if err := yamledit.ApplyJSONPatchAtPathBytes(doc, patch, []string{"service", "externalSecretEnvs"}); err != nil { /* ... */ }
out, _ := yamledit.Marshal(doc)
```

**Example: append a new array item**

```go
patch := []byte(`[{"op":"add","path":"/-","value":{"name":"EXTRA","path":"data/shared","property":"extra"}}]`)
_ = yamledit.ApplyJSONPatchAtPathBytes(doc, patch, []string{"service", "externalSecretEnvs"})
out, _ := yamledit.Marshal(doc)
```

---

## Guarantees & design choices

* **Comments preserved.** For edits made through this package, header, foot, and inline (`# ...`) comments are
  preserved; unrelated lines are byte‑stable.
* **Indent preserved.** Base indent auto‑detected (2/3/4/…); indentless sequences supported; new content matches
  original style.
* **Key order preserved.** Original order is maintained; **new keys are appended** to their mapping.
* **Duplicates deduped when safe.** When exact source bounds are available, earlier duplicate keys are removed and the
  **last** occurrence remains (YAML semantics: last wins). Duplicates in source forms that cannot be bounded safely are
  preserved rather than risking removal of neighboring content.
* **Booleans normalize on edit.** A key you edit with `SetScalarBool` (or via JSON Patch) will render as bare `true`/
  `false` even when its source token is quoted. Unrelated booleans remain untouched.
* **Implicit nulls stay null.** An untagged blank mapping value such as `config:` remains a YAML null and is byte-stable
  across a no-op parse/marshal cycle. `EnsurePath` explicitly converts it to a mapping when a caller asks to traverse
  or populate that path.
* **No global re‑encode for package edits.** Mutations made through `EnsurePath`, setters, `DeleteKey`, or JSON Patch use
  surgery or per-key/sequence rewrites based on recorded bounds. If those are unsafe, `Marshal` returns an error.
  Direct field changes to the returned `yaml.Node` are the exception: because they bypass the edit index, `Marshal`
  globally encodes the live AST to honor them, which may reflow formatting.
* **Direct AST access is caller-synchronized.** Do not mutate fields on the returned `yaml.Node` concurrently with
  yamledit API calls. The thread-safety guarantee covers calls made through the package APIs, not unsynchronized raw
  field writes.
* **Sequence append/delete supported.** Scalar arrays can be appended to or truncated surgically; complex reorders may
  still be unsupported and will error rather than churn bytes.

---

## Arrays (sequences)

* **Arrays of mappings**

    * In‑place updates (e.g. change `property` of item `0`) are typically **single‑line** surgical diffs.
    * Appends render using the item’s captured style:

      ```
      - name: FOO
        path: ...
        property: ...
      ```
* **Arrays of scalars**

    * Index‑based replacements can be surgical.
    * **Whole‑array replace** may fall back and can drop inter‑item comments. If you need minimal diffs & comment
      preservation, prefer targeted index edits and `/-` appends instead of replacing the entire list.

---

## Testing

The suite covers:

* quote preservation (single/double), inline comments, final newline,
* exact indent (2/3/4‑space, indentless),
* new key insertion & append order,
* JSON Patch on scalars, maps, arrays,
* duplicate removal, deletions (including arrays),
* concurrency safety.

Run:

```bash
go test ./...
```

## Performance

Parsing and indexing are linear in document size. A registered mutation may locate its target and snapshot the full
document, and `Marshal` validates the complete live/output graph. Bulk helpers repeat mutation work per field, sorting
`k` map keys adds O(k log k), and presentation reconciliation depends on the changed collection; total cost is therefore
not merely O(changes). Memory use scales with the source buffer, AST/shadow snapshots, and source indices.

The benchmark suite provides allocation-aware small and large cases for Parse, no-op Marshal, scalar surgery,
structural and sequence replacement, multi-operation JSON Patch, and wide mapping/sequence presentation reconciliation.

---

## License

The repository does not yet contain a `LICENSE` file. The maintainer must
select the license text and copyright notice before a release is published.
