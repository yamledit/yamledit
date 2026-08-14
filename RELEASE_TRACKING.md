# Unreleased correctness release

This document tracks the work required to turn the correctness hardening in
`0c9ad45` into a release-ready change. A version number has not been selected;
the completed compatibility audit recommends treating the changes as
major-level because ordinary `SetValue` semantics changed.

## Release goals

- Preserve the byte-stability and YAML-semantic guarantees documented in the
  README.
- Detect parser, patch, mutation-history, alias, and presentation regressions
  automatically.
- Measure the cost of correctness validation on representative documents.
- Publish explicit compatibility and migration guidance for changed behavior.
- Reduce duplicated source-surgery logic where a test-backed refactor makes
  invariants easier to maintain.
- Run the supported test matrix in CI on every pull request and push to `main`.

## Workstreams

| Workstream | Status | Exit criteria |
| --- | --- | --- |
| Correctness baseline | Complete | `0c9ad45` is on `main`; normal, race, vet, shuffle, and Go 1.24.1 tests pass. |
| Fuzz/property coverage | Complete | Seeded, bounded fuzz targets cover Parse/Marshal, JSON Patch atomicity and semantics, aliases, duplicates, multiline/flow YAML, and composed mutation histories. |
| Compatibility audit | Complete | `CHANGELOG.md` classifies source compatibility, intentional semantic changes, stricter validation, direct AST behavior, and JSON Patch constraints against `3919c17`. |
| Benchmarks | Complete | Parse, no-op Marshal, scalar surgery, structural/sequence edits, JSON Patch, and wide presentation reconciliation have reproducible benchmarks. |
| Surgery simplification | Complete | Append and whole-sequence rewrites share ordered-path lookup, mapping coercion, scalar rendering, and one sequence-mapping renderer. |
| CI hardening | Implemented; hosted run pending | `.github/workflows/ci.yml` covers Linux/macOS/Windows, Go 1.24.1/current, race, vet, shuffle, fuzz smoke, changed-line whitespace checks, formatting, and benchmark smoke. The release commit must pass the hosted matrix. |
| Release notes | Complete | `CHANGELOG.md` records the unreleased changes, limitations, compatibility recommendation, and upgrade checklist without assigning a version. |
| Licensing | Pending maintainer decision | Confirm the intended license and copyright notice, then add the corresponding root `LICENSE` file. |
| Release publication | Pending maintainer decision | Select the major-level version, merge a release commit with green hosted CI, then create the tag and published release from that exact commit. |

## Compatibility questions

- [x] Classify `SetValue` map replacement, empty collection, numeric-category,
  invalid/cyclic input, and `DeleteEmptyStrings` semantics.
- [x] Classify stricter malformed-AST, alias-graph, JSON Patch member, and root
  path validation.
- [x] Document direct `yaml.Node` mutation formatting and synchronization rules.
- [x] Decide the recommended semantic-version increment and record why.
- [x] Identify any behavior that needs a compatibility shim before release.

## Required verification

- [x] `go test ./...`
- [x] `go test -race ./...`
- [x] `go vet ./...`
- [x] `go test ./... -shuffle=on -count=20`
- [x] `GOTOOLCHAIN=go1.24.1 go test ./...`
- [x] Fuzz seed corpus passes as ordinary tests.
- [x] Each fuzz target completes a bounded smoke run.
- [x] Benchmarks compile and complete a short smoke run.
- [x] `gofmt` and `git diff --check` are clean.
- [x] No temporary probe, corpus-crash, or generated profile files remain.
- [ ] Hosted CI matrix passes on the exact release commit.
- [ ] Maintainer confirms licensing and adds the root `LICENSE` file.
- [ ] Maintainer selects the version and confirms publication timing.
- [ ] Release tag and published notes point at the verified release commit.

## Release decision log

| Date | Decision | Rationale |
| --- | --- | --- |
| 2026-08-14 | Treat licensing as a publication gate; do not synthesize a `LICENSE` file during technical hardening. | The README named MIT, but the repository contains no license grant and the correct copyright holder/year require maintainer confirmation. |
| 2026-08-14 | Keep the work “Unreleased” until a version is selected and hosted CI passes on the release commit. | The repository has no conventional semantic-version tags. The compatibility class is now known, but the maintainer still needs to choose the first conventional version and publication timing. |
| 2026-08-14 | Recommend a major-level compatibility release; do not assign a version in this audit. | Exported signatures are stable, but ordinary `SetValue` calls change map merge/replacement, empty-collection, and numeric-tag behavior. Those are observable semantic breaks. |
| 2026-08-14 | Do not add a legacy compatibility shim before release. | Callers can request the old merge behavior explicitly with `EnsurePath` plus `SetMapValues`; retaining two meanings for `SetValue` would keep the ambiguous contract that this hardening resolves. |

## Deferred follow-ups

Items belong here only when they are explicitly judged non-blocking for this
release, with a reason and an owner or tracking reference. The section is empty
until the audits establish such items.
