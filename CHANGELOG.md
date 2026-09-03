# Changelog

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and
the version axes are the ones SPEC.md §30.1 separates: the compiler crate and
binary carry the SemVer below, each project selects the supported language
identifier (`1.0` or `1.1`), and each language's compiler-semantics ID is a
digest over its normative language data, schemas, and pinned golden fixtures.

SPEC.md §2.3 fixes `0.1.0` as the initial implementation version and `1.0.0` as
the first release satisfying the complete specification. No tag before `1.0.0`
is therefore a §30 release: `cargo xtask release-check` reads the complete
§30.3 artifact set and §30.4 completion criterion and refuses, naming every
criterion that does not hold. That refusal is the accurate answer at these
versions, and the entries below say what each tag does and does not claim.

## 0.2.0

Language 1.1 gains the closed portable data and operation vocabulary required
by generated application runtimes. This is the immutable PrismPM integration
line; it does not weaken the separate LexLean 1.0.0 full-spec release gate.

### Implemented

- Distinct mathematical `Int` and fixed-width signed/unsigned integer types,
  UTF-8 strings, byte sequences, ordering, option, and result values, with
  canonical checked literals and no implicit host-width conversion.
- Twenty-eight generic typed operations covering checked arithmetic and
  conversion, quotient/remainder zero cases, bit operations and bounded
  shifts, collections and byte ranges, UTF-8, byte ordering, bounded exact
  split/join, and canonical decimal parse/format.
- One fixed Lean 4.32.1 runtime lowering and canonical LaTeX rendering for the
  portable vocabulary. Definitions and theorems both carry exact observed
  axiom policies; verification still elaborates, replays with `leanchecker`,
  and audits every policy.
- `SM-17` through `SM-22`, an all-operation semantic fixture, exhaustive
  fixed-width bound/signature tests, schema validation, malformed-input cases,
  and cross-root snapshot identity checks. The register now contains 222
  implemented capability IDs.

### Compatibility

- Language 1.0 syntax and meaning are unchanged. Language 1.1 and
  `lexlean/semantic-snapshot/1` are extended in place under the ecosystem's
  pre-freeze policy; their compiler-semantics digest and affected expected
  artifacts are regenerated.
- No Prism-, Holo-, or Calculator-specific node, raw Lean/Rust field, macro,
  tactic, or backend escape hatch is added.

### Not claimed

- This remains an integration release rather than the complete LexLean §30
  release, which is intentionally reserved for version 1.0.0.

## 0.1.1

The UOR Atlas becomes the foundation model of LexLean: every accepted document
carries the Atlas-derived header, and the Atlas formalization is closed inside
the repository.

### Implemented

- The one-time Atlas conversion is closed and recorded in
  `examples/uor-atlas/MIGRATION.md`; its independently authored Lean source and
  exporter are absent from the release tree. `VR-19` now permanently audits
  the native source graph itself: every source module has one generated Lean
  module, public imports stay within `Init` and the generated graph, the only
  backend-support import is `Lean`, and no second Atlas implementation exists.
  `just vv` verifies the generated native Atlas
  under `leanprover/lean4:v4.32.1`, replays it through `leanchecker` — a
  same-kernel replay, not an independent checker (§22.4) — and runs the
  standing exact axiom gate.
- Two new built-in lexicon packages, `lexlean.std.int@1.0.0` and
  `lexlean.uor.atlas@1.0.0`. The Atlas package is registered under
  `[[builtin_package]]`, locked into every project, and unconditionally
  visible in every document, so the header is carried whether or not a
  document names an Atlas entry; its visibility closes transitively over
  `lexlean.core`, `lexlean.std.nat`, and `lexlean.std.int`.
- The frozen Atlas pack is complete against the native source register: every
  label carries exactly one disposition, the registers key on exact
  identifiers, and every frozen entry refers to a declaration owned by the
  native source rather than importing an independently authored module.
  Coverage begins at `Atlas.lex.tex`; exercise, denotation,
  surface-disjointness, and authority-scope audits run as gates,
  each with a planted-defect record in VERIFICATION.md.
- `examples/uor-atlas/` verifies under the pinned toolchain with its
  committed verification records, and the negative fixture suite grows to 28
  classes with `atlas-level-conflation`, rejected by `LLR3005`: a native Atlas
  document declaration cannot be consumed as an external glossary atom.
- `examples/uor-atlas/src/Atlas.lex.tex` is the single native semantic and
  proof source for 5,519 environment declarations; 58 private source-compiler
  implementation records remain hashed provenance and are emitted by neither
  backend. Both backends traverse that closed DAG, generated Lean publicly
  imports only `Init` and generated Atlas modules, privately imports only the
  generic `Lean` support module, and contains no independently authored Atlas
  implementation.
  `S43` is authoritatively the proved integer-uniqueness statement.
  `SM-15` and `VR-19` bring the register to 211 IDs, all implemented at level
  `build`.
- Language `1.1` adds a closed generic semantic declaration, term, and proof
  language for structures, classes, instances, finite inductives, total
  structural recursion, exhaustive matches, Boolean validators, exact theorem
  application, and axiom-free Boolean reflection. Its seven-module
  `semantic-1.1` fixture contains no handwritten Lean and exercises every
  closed variant through elaboration, `leanchecker`, and exact axiom audit.
- The stable seventh `Engine` operation returns an owned, read-only,
  path-independent `lexlean/semantic-snapshot/1` DTO. The public DTOs and
  complete closed JSON Schema expose every legal semantic module variant while
  keeping mutable compiler internals and both fixed backends private. `SM-16`,
  `DF-11`, `CF-16`, `CL-19`, and `CL-20` bring the register to 216 IDs, all
  implemented at level `build`.

### Changed

- Generated-module verification passes Lean an explicit package root with
  `-R`. This removes random staging paths from `.olean` serialization, so a
  same-platform verification has byte-identical oleans and an identical
  attestation across absolute project roots.
- The compiler-semantics ID moves from
  `fa171c7a2d78cf17e6cb49bbec5c1eed8bee20033472b1953211104068589ba7` to
  `95deb33a8d416d7bf60f02a36e251a71c3ee6f046b7e475d7bae2fc5ddc3767d`:
  the accepted language changed, so §30.1 requires a new ID. Every committed
  lock and verification record is regenerated against it.
- Language `1.1` has its independent compiler-semantics ID
  `0accaf7b80d572e21451d5fa650d92a1a28dae799823931b2f756e448fe89996`;
  language-1.0 locks and generated artifacts remain byte-identical.
- The four 0.1.0 examples still format byte-identically and generate
  byte-identical Lean and LaTeX modules; their source maps and manifests
  differ only in the source and semantic digests those artifacts embed. No
  previously-accepted run changed its generated bytes (§30.2).

### Not claimed

- This is not a §30 release. `cargo xtask release-check` refuses at `0.1.1`,
  and the release criterion is met only at `1.0.0`.
- The native Atlas graph's verification status is a `build` claim: it elaborates,
  replays, and reports no axiom outside Lean's own. The mathematical content
  is the specification's, cited at `some-true`, and the Lean kernel and
  elaborator beneath it are cited, not verified; the honest claim is that the
  Atlas is as sound as Lean 4.32.1, not that it is sound absolutely.
- Verified status is claimed by `verify` alone. `check` and `build` never
  claim it (`VR-18`), and `leanchecker` is a same-kernel replay, never
  described as an independent checker (§22.4).

## 0.1.0

The initial implementation of `LEXLEAN-SPEC-1`.

### Implemented

All 216 conformance IDs of SPEC.md §31 are implemented at honesty level
`build`: constructed in this repository and validated against an oracle by the
test named `conformance_<id>`. [CONFORMANCE.md](CONFORMANCE.md) is the
generated register, [ERRORS.md](ERRORS.md) the closed diagnostic registry, and
[VERIFICATION.md](VERIFICATION.md) the falsifiability record for every gate.

- Closed project configuration, canonical lock file, and offline dependency
  policy (`CF-01`..`CF-16`).
- Total lexical closure over every accepted atom (`LX-01`..`LX-14`) and
  versioned lexicon packages with closed schemas, denotations, and renderer
  tokens (`GL-01`..`GL-16`).
- The fixed structural, mathematical, and proposition grammar with closed
  ambiguity handling (`GR-01`..`GR-16`), the typed closed IR with canonical
  serialization, native modules, and language-1.1 snapshots (`SM-01`..`SM-16`),
  and generic semantic declarations plus document definitions with exact
  self-application and acyclicity rules (`DF-01`..`DF-11`).
- The structured proof language with pinned Lean lowerings (`PF-01`..`PF-18`),
  prose-free deterministic generated Lean with complete token traceability
  (`LN-01`..`LN-12`), and canonical LaTeX regeneration with the optional
  hash-checked PDF provider (`TX-01`..`TX-12`).
- Canonical diagnostics, source maps, coverage, manifests, and reproducible
  builds (`AR-01`..`AR-14`); fifteen-stage verification with `leanchecker`
  replay and exact axiom audit (`VR-01`..`VR-19`); the exact CLI contract and
  the stable seven-method Rust `Engine` API (`CL-01`..`CL-20`); filesystem
  confinement, no shell, no hidden network, and the closed failure model
  (`SE-01`..`SE-12`).
- Six example projects that verify under the pinned `leanprover/lean4:v4.32.1`
  toolchain, and the complete negative fixture suite (`EX-01`..`EX-08`).

### Not claimed

- This is not a §30 release. `cargo xtask release-check` refuses at `0.1.0`,
  and the release criterion is met only at `1.0.0`.
- Verified status is claimed by `verify` alone. `check` and `build` never claim
  it (`VR-18`), and `leanchecker` is a same-kernel replay, never described as
  an independent checker (§22.4).
- Facts about external tools are level `some-true` rows in
  [`model/ledger.toml`](model/ledger.toml): reproduced from cited authorities,
  not established here.
- The normative verification and reproducibility gate runs on Linux x86-64
  (§8.3). The other four supported hosts build the crate and run every test
  that does not need the pinned toolchain or a POSIX shell; each such case
  reports which assertions it did not run.

### Known deviations

The README's "Documented deviations" section lists every place the generated
bytes differ from a literal reading of SPEC.md, with the reason. Each is
enforced by the same golden and conformance gates as everything else.
