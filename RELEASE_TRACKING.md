# Release readiness

This document tracks the work required to publish the hardened yamledit
implementation. The intended API semantics are fixed; a release version has not
yet been selected.

## Release goals

- Preserve the byte-stability and YAML-semantic guarantees documented in the
  README.
- Detect parser, patch, mutation-history, alias, and presentation regressions
  automatically.
- Measure correctness-validation costs on representative documents.
- Keep the source-surgery implementation small enough that its invariants can be
  audited and tested directly.
- Run the supported test matrix in CI on every pull request and push to `main`.
- Publish concise documentation for the final API behavior and known limits.

## Workstreams

| Workstream | Status | Exit criteria |
| --- | --- | --- |
| API semantics | Complete | `SetValue`, `SetMapValues`, deletion, numeric typing, JSON Patch, and direct-AST behavior are defined and tested consistently. |
| Correctness hardening | Complete | Silent corruption, alias, multiline-boundary, tag-intent, ordering, comment, and malformed-AST cases have permanent regressions. |
| Fuzz/property coverage | Complete | Seeded, bounded fuzz targets cover Parse/Marshal, JSON Patch atomicity and semantics, aliases, duplicates, multiline/flow YAML, and composed mutation histories. |
| Benchmarks | Complete | Parse, no-op Marshal, scalar surgery, structural/sequence edits, JSON Patch, and wide presentation reconciliation have reproducible benchmarks. |
| Surgery simplification | Complete | Append and whole-sequence rewrites share ordered-path lookup, mapping coercion, scalar rendering, and one sequence-mapping renderer. |
| CI hardening | Implemented; green run pending | `.github/workflows/ci.yml` covers Linux/macOS/Windows, Go 1.24.1/current, race, vet, shuffle, fuzz smoke, changed-line whitespace checks, formatting, and benchmark smoke. |
| Release notes | Complete | `CHANGELOG.md` describes the final semantics, safety guarantees, JSON Patch rules, correctness work, and engineering coverage. |
| Licensing | Pending maintainer decision | Confirm the intended license and copyright notice, then add the corresponding root `LICENSE` file. |
| Publication | Pending maintainer decision | Select a version, merge a release commit with green hosted CI, and create the tag and published release from that exact commit. |

## Required verification

- [x] `go test ./...`
- [x] `go test -race ./...`
- [x] `go vet ./...`
- [x] `go test ./... -shuffle=on -count=20`
- [x] `GOTOOLCHAIN=go1.24.1 go test ./...`
- [x] Fuzz seed corpus passes as ordinary tests.
- [x] Each fuzz target completes a bounded local smoke run.
- [x] Benchmarks compile and complete a short smoke run.
- [x] `gofmt` and `git diff --check` are clean.
- [x] No temporary probe, corpus-crash, or generated profile files remain.
- [ ] Hosted CI passes on the exact release commit.
- [ ] Maintainer confirms licensing and adds the root `LICENSE` file.
- [ ] Maintainer selects the version and publication timing.
- [ ] Release tag and published notes point at the verified release commit.

## Release decisions

| Date | Decision | Rationale |
| --- | --- | --- |
| 2026-08-14 | Keep the work unreleased until a version is selected and hosted CI passes on the release commit. | A release should point to the exact commit that passed the complete hosted matrix. |
| 2026-08-14 | Treat licensing as a publication gate and do not synthesize a license grant during technical hardening. | The correct license, copyright holder, and year require maintainer confirmation. |
| 2026-08-14 | Use explicit, orthogonal value APIs. | `SetValue` replaces a value, `SetMapValues` merges fields, and deletion is requested with `DeleteKey` or direct nil. |

## Deferred follow-ups

Items belong here only when explicitly judged non-blocking for release, with a
reason and an owner or tracking reference. The section is currently empty.
