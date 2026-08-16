# VERIFICATION

How this repository's claims are checked, which recipe enforces which rule, and the evidence that each gate can actually fail. A gate nobody has seen fail is indistinguishable from a gate that cannot (§27.9).

## The acceptance gate

`just vv` runs, in the normative order (SPEC.md §9.2):

| Recipe | Command | Rules it enforces |
| --- | --- | --- |
| `fmt-check` | `cargo fmt --all -- --check` | one canonical source formatting |
| `model` | `cargo xtask validate-model` | R1 (model is the single source), R2 (honesty levels, via the meta-gate), R4 (`audit-deferral`), R5 (`audit-errors`), R6 (`audit-shipped`), R8 (`audit-generated`, `audit-language-closure`), RP-09 (`audit-no-unsafe`), §27.5 (CONFORMANCE.md and ERRORS.md equal regeneration) |
| `spec-links` | `cargo xtask validate-spec-links` | RP-07, §27.6: the §31 table and `model/ids.toml` are bijective and byte-consistent |
| `lint` | `cargo clippy --workspace --all-targets --all-features -- -D warnings` | no tolerated warnings |
| `test` | `cargo test --workspace --all-features` | §28.1 classes 1–2 and 4–5 (unit, property, integration, CLI) plus all 209 conformance tests |
| `features` | `cargo check --workspace --all-features --all-targets` | every target compiles |
| `bdd` | `cargo test -p repo-conformance` | R3, §27.7, §27.8: register ↔ scenario ↔ test bijection, the meta-gate, and its own falsifiability test |
| `examples` | `cargo xtask verify-examples` | §28.6, EX-01: every example directory formats, locks, checks, builds, and verifies with real Lean 4.32.1 |
| `golden` | `cargo xtask check-golden` | R10, §28.3: build outputs equal the committed oracles byte for byte |
| `repro` | `cargo xtask check-reproducibility` | AR-13, §28.4: two clean builds in distinct absolute directories are byte-identical |
| `deny` | `cargo deny --all-features check` | advisories, bans, licenses, sources |

`just release` additionally runs `cargo xtask release-check` (RP-12) and is refused until every §30.3 artifact and the §30.4 completion criterion exist.

## What the claims mean

- Every §31 conformance ID is level `build` (§27.3): constructed here and validated against its oracle by the test `conformance_<id>`. Evidence, not a proof.
- Facts about Lean 4.32.1, Lake, `leanchecker`, and `#print axioms` output are `some-true` rows in `model/ledger.toml`: reproduced from the cited authority rows in `model/authorities.toml`, not established here.
- `lexlean verify` is the only command that runs Lean; its attestation records toolchain hashes, per-process records, and per-declaration observed axiom sets, and its ID is recomputed by `conformance_vr_14`.

## Falsifiability records

Each gate below was made to fail by planting a defect, the failure was recorded, and the defect was removed. The records are verbatim gate output.

### spec-links can fail (RP-07)

Planted: one word removed from one `model/ids.toml` statement.

```text
  table:    The repository, crate, executable, metadata, and licenses have the exact LexLean identity specified.
  register: The repository, crate, executable, metadata, and licenses have the exact identity specified.
```

Removed: the register row was restored; `validate-spec-links` reports 209 bijective rows again.

### audit-deferral can fail (R4)

Planted: a deferral marker (spelled here in halves: `TO` + `DO`) appended as a comment to `crates/lexlean/src/fmt.rs`.

```text
gate failed: R4: nothing is deferred. None of TODO, FIXME, XXX, unimplemented!, todo!, for now, later version may appear outside a code span.
```

Removed: the comment was deleted; `audit-deferral` reports nothing deferred.

### check-golden can fail (R10)

Planted: one bit flipped in the committed oracle `examples/nat-add-zero/expected/build/manifest.json`.

```text
gate failed: R10: nat-add-zero: manifest.json differs from its committed oracle; a semantic change needs `just golden-write` and review (§28.3)
```

Removed: the oracle byte was restored; `check-golden` reports 6 artifacts equal.

### a conformance test can fail (AR-11)

Planted: `Json::to_file_bytes` was changed to omit the final LF, erasing the §21.7 hash-form/file-form distinction.

```text
thread 'conformance_ar_11' (...) panicked at crates/conformance/src/cases/artifacts.rs:...:
assertion `left == right` failed: file form adds exactly one final LF; the hash form has none
test result: FAILED. 0 passed; 1 failed; ...
```

Removed: the LF push was restored; `conformance_ar_11` passes.

### the meta-gate can fail (R2/R3)

`crates/conformance/tests/bdd.rs::the_meta_gate_is_falsifiable_cm_02` plants an empty workspace test list on every run and asserts the missing-test violation is reported. This record re-establishes itself on every `just vv`.

## End-to-end Lean evidence

The literal §29 example verifies against real `leanprover/lean4:v4.32.1`: probe elaboration, module compilation, separate-process `leanchecker` replay, exact `#print axioms` parsing, and the `\noaxioms` policy over an empty observed set (`conformance_ex_01`). The required §29.6 mutations are mechanized: a false proposition fails inside Lean and remaps to the source proof sentence (`conformance_ex_02`, `conformance_pf_18`); an undeclared title word fails lexical closure (`conformance_ex_03`); an indistinguishable same-surface entry is ambiguity, never priority (`conformance_ex_04`); an insufficient axiom allow-list fails policy checking with the observed excess recorded (`conformance_ex_05`, `conformance_vr_16`); and two clean builds in distinct paths are byte-identical (`conformance_ex_06`, plus `just repro`).
