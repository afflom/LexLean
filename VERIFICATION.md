# VERIFICATION

How this repository's claims are checked, which recipe enforces which rule, and the evidence that each gate can actually fail. A gate nobody has seen fail is indistinguishable from a gate that cannot (SPEC.md §27.9).

## The acceptance gate

`just vv` runs, in the normative order (SPEC.md §9.2):

| Recipe | Command | Rules it enforces |
| --- | --- | --- |
| `fmt-check` | `cargo fmt --all -- --check` | one canonical source formatting |
| `model` | `cargo xtask validate-model` | R1 (model is the single source; every model file parsed with unknown-field rejection), R2 (honesty levels and vocabulary, via the meta-gate), R3 (register/scenario/test bijection, Gherkin subset), R4 (`audit-deferral`), R5 (`audit-errors`), R6 (`audit-shipped`, including the shipped crate's normative links), R8 (`audit-generated`, `audit-language-closure`), RP-09 (`audit-no-unsafe`), §27.5 (CONFORMANCE.md and ERRORS.md equal regeneration) |
| `spec-links` | `cargo xtask validate-spec-links` | RP-07, §27.6: the §31 table and `model/ids.toml` are bijective and byte-consistent |
| `lint` | `cargo clippy --workspace --all-targets --all-features -- -D warnings` | no tolerated warnings |
| `test` | `cargo test --workspace --all-features` | §28.1 classes 1–2 and 4–5 (unit, property, integration, CLI), the model crate's own tests, and all 209 conformance tests, which include the §28.2 fixture suite (`conformance_ex_07`) and the crate-packaging round trip (`conformance_rp_12`) |
| `features` | `cargo check --workspace --all-features --all-targets` | every target compiles |
| `bdd` | `cargo test -p repo-conformance` | R3, §27.7, §27.8: register ↔ scenario ↔ test bijection, the meta-gate, and its own falsifiability test |
| `examples` | `cargo xtask verify-examples` | §28.6, EX-01: every example directory formats, locks, checks, builds, and verifies with real Lean 4.32.1; when an example commits `expected/verify/`, its normalized verification records must equal it (§29.5) |
| `golden` | `cargo xtask check-golden` | R10, §28.3: the *published* build tree of a real `build` in a fresh directory equals the committed oracles byte for byte |
| `repro` | `cargo xtask check-reproducibility` | AR-13, §28.4: two clean `build`s in distinct absolute directories publish byte-identical trees with no absolute path inside |
| `deny` | `cargo deny --all-features check` | advisories, bans, licenses, sources |

Outside `vv`:

- `just fixtures` (`cargo xtask check-fixtures`) runs every §28.2 fixture under `tests/fixtures/` and `tests/negative/` through the CLI entry point and compares exit code, canonical command result, diagnostics, artifact list, and platform-independent hashes with `expected/`. `just fixtures-write` is the only rewrite path.
- `just verify-write` (`cargo xtask verify-examples --write`) is the only path that rewrites `examples/*/expected/verify/`.
- `just release` runs `vv` and then `cargo xtask release-check` (RP-12): every §30.3 artifact by content, the §30.4 completion criteria, and the crate-packaging round trip (`cargo package`, extract, offline build, `--version` equal to the in-repository binary). It is refused until 1.0.0.

## What the claims mean

- Every §31 conformance ID is level `build` (§27.3): constructed here and validated against its oracle by the test `conformance_<id>`. Evidence, not a proof.
- Facts about Lean 4.32.1, Lake, `leanchecker`, and `#print axioms` output are `some-true` rows in `model/ledger.toml`: reproduced from the cited authority rows in `model/authorities.toml`, not established here.
- `lexlean verify` is the only command that runs Lean; its attestation records toolchain hashes, per-process records, and per-declaration observed axiom sets, and its ID is recomputed by `conformance_vr_14`.
- Lean-backed conformance cases detect the host at run time (`repo_conformance::support::lean_backed`): on Linux x86-64 the pinned toolchain is mandatory and a missing toolchain fails the case; on another supported host without the toolchain the case runs only its platform-independent assertions and prints that it did (§8.3).

## Falsifiability records

Each gate below was made to fail by planting a defect, running the gate's command, recording the failure, and removing the defect. The observed lines are verbatim gate output (paths abbreviated to the repository root). `cargo xtask release-check` requires a `### <gate> can fail` record for every gate and audit named in `repo_model::release::GATES`.

### fmt-check can fail

Planted: `fn   badly_formatted( ) {}` appended to `crates/model/src/release.rs`. Command: `cargo fmt --all -- --check`. Expected: a formatting diff and a nonzero exit.

```text
Diff in crates/model/src/release.rs:578:
-fn   badly_formatted( ) {}
+fn badly_formatted() {}
exit=1
```

Removed: the line was deleted; `cargo fmt --all -- --check` is silent.

### validate-model can fail

Planted: the generated `CONFORMANCE.md` edited so that `RP-01`'s level cell reads `open`. Command: `cargo xtask validate-model`. Expected: the committed document no longer equals regeneration (R1).

```text
gate failed: CONFORMANCE.md is stale: it disagrees with model/*.toml (R1). Run `just model-write`.
```

Removed: the document was restored; the gate reports documents current.

### audit-deferral can fail

Planted: a deferral marker (spelled here in halves: `TO` + `DO`) appended as a comment to the `Justfile`, which is inside the audit's root-tooling scope. Command: `cargo xtask validate-model`. Expected: R4 names the file and line.

```text
gate failed: R4: nothing is deferred. None of TODO, FIXME, XXX, unimplemented!, todo!, for now, later version may appear outside a code span.

Justfile:86: # TODO: tighten this later
```

Removed: the comment was deleted; `audit-deferral` reports nothing deferred.

### audit-errors can fail

Planted: the literal `"LLL1004"` in `crates/conformance/src/cases/lexical_closure.rs` changed so that its third digit is `9` (a well-shaped but unregistered code) outside any `code!(` invocation. Command: `cargo xtask validate-model`. Expected: R5 rejects the unregistered literal at its line.

```text
gate failed: R5: crates/conformance/src/cases/lexical_closure.rs:203: `LLL1<9>4` is not a registered diagnostic code (§26.1)
```

Removed: the literal was restored; `audit-errors` reports 47 registered codes, every one constructed by the shipped crate.

### audit-shipped can fail

Planted: the in-crate link `crates/lexlean/schemas` repointed at `../../tests`. Command: `cargo xtask validate-model`. Expected: R6 reports the link resolves elsewhere than the repository's `schemas/`.

```text
gate failed: R6: crates/lexlean/schemas resolves to <root>/tests rather than schemas; the crate must embed the repository's own normative data
```

Removed: the link was restored to `../../schemas`; `audit-shipped` reports the links resolve.

### audit-generated can fail

Planted: `schemas/coverage.schema.json` re-serialized with indentation (no longer canonical JSON). Command: `cargo xtask validate-model`. Expected: the schema is rejected as non-canonical.

```text
gate failed: R10: <root>/schemas/coverage.schema.json is not canonical JSON; regenerate the schema
```

Removed: the schema bytes were restored; `audit-generated` reports 9 schemas canonical.

### audit-language-closure can fail

Planted: a `[[token]]` row `orphan-token` appended to `language/renderer-tokens.toml` that no preamble construct or LRE references. Command: `cargo xtask validate-model`. Expected: R8 rejects the unused registry row (§13.10).

```text
gate failed: R8: unused registry rows fail the language audit (§13.10): ["orphan-token"]
```

Removed: the row was deleted; the audit reports 72 tokens equal to the referenced closure.

### audit-no-unsafe can fail

Planted: the `#![forbid(unsafe_code)]` line removed from `crates/lexlean/src/lib.rs`. Command: `cargo xtask validate-model`. Expected: the audit reports the crate-level prohibition missing (RP-09).

```text
gate failed: R6: crates/lexlean/src/lib.rs must carry the crate-level prohibition
```

An `unsafe` block planted in `crates/lexlean/src/error.rs` instead does not even reach the audit: `rustc` refuses the crate under the prohibition (`error: usage of an `unsafe` block`, exit 101). Removed: the attribute was restored; the audit reports the prohibition active.

### honesty-vocabulary can fail

Planted: the sentence "The authority `LEAN-REL-4-32-1` proves every generated theorem." appended to `README.md`. Command: `cargo xtask validate-model`. Expected: R2 rejects assertive vocabulary about a cited authority.

```text
gate failed: the honesty meta-gate failed inside validate-model:

R2: README.md:110: `LEAN-REL-4-32-1` is cited, not established here, but this line says `proves`.
```

Removed: the sentence was deleted; the vocabulary check is clean.

### meta-gate can fail

Planted: the tag line of `LX-06` in `features/suites/lexical-closure.feature` changed to `@LX-06 @open`. Command: `cargo xtask validate-model`. Expected: R2 rejects the level drift between register and scenario.

```text
gate failed: the honesty meta-gate failed inside validate-model:

R2: LX-06's tag line must be exactly `@LX-06 @build`, found `@LX-06 @open` (§27.7).
```

Removed: the tag was restored. `crates/conformance/tests/bdd.rs::the_meta_gate_is_falsifiable` re-establishes this record on every run: it plants an empty test list, a reordered tag line, a drifted statement, and a pending step, and asserts each is reported; `a_hidden_conformance_test_is_flagged` plants a `cfg_attr(..., ignore)` attribute and asserts the attribute-block scanner flags it.

### model-unknown-field can fail

Planted: `priority = "high"` appended to `model/ids.toml`. Command: `cargo xtask validate-model`. Expected: the model parser rejects the unknown field (§27.5 step 1).

```text
gate failed: parsing <root>/model/ids.toml: TOML parse error at line 1264, column 1
     |
1264 | priority = "high"
     | ^^^^^^^^
unknown field `priority`, expected one of `id`, `level`, `suite`, `statement`
```

Removed: the row was deleted. `crates/model/src/lib.rs::unknown_fields_are_rejected_in_every_model_file` re-plants an unknown field at the top level and inside a row of each of the four model files on every `cargo test`.

### spec-links can fail

Planted: one word removed from the `RP-03` statement in `model/ids.toml`. Command: `cargo xtask validate-spec-links`. Expected: RP-07 reports the table/register disagreement.

```text
gate failed: RP-07: `RP-03`'s statement differs between the table and the register:
  table:    The completed repository has the required file and crate layout.
  register: The completed repository has the required layout.
```

Removed: the register row was restored; the gate reports 209 bijective rows.

### lint can fail

Planted: `fn planted_unused() { let unused_value = 1; }` appended to `crates/model/src/release.rs`. Command: `cargo clippy --workspace --all-targets --all-features -- -D warnings`. Expected: warnings are errors.

```text
error: unused variable: `unused_value`
error: function `planted_unused` is never used
error: could not compile `repo-model` (lib) due to 2 previous errors
```

Removed: the function was deleted; clippy is clean.

### test can fail

Planted: the last hex digit of the empty-input SHA-256 vector in `crates/model/src/release.rs` changed from `5` to `6`. Command: `cargo test -p repo-model --all-features`. Expected: the unit test fails on the digest.

```text
thread 'release::tests::the_local_sha256_agrees_with_the_test_vectors' panicked at crates/model/src/release.rs:566:9:
assertion `left == right` failed
  left: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
 right: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b856"
test result: FAILED. 3 passed; 1 failed
```

Removed: the vector was restored. A conformance test fails the same way: `Json::to_file_bytes` changed to omit its final LF fails `conformance_ar_11` (`file form adds exactly one final LF; the hash form has none`).

### features can fail

Planted: `fn planted() -> u32 { "not a number" }` appended to `crates/conformance/tests/bdd.rs`, a test target. Command: `cargo check --workspace --all-features --all-targets`. Expected: the test target does not compile.

```text
error[E0308]: mismatched types
error: could not compile `repo-conformance` (test "bdd") due to 1 previous error
```

Removed: the function was deleted; every target checks.

### bdd can fail

Planted: the `EX-08` scenario removed from `features/suites/examples.feature`. Command: `cargo test -p repo-conformance --test bdd`. Expected: R3 reports the registered ID with no scenario.

```text
test every_id_has_a_scenario_and_a_test ... FAILED
the honesty meta-gate failed:

R3: EX-08 is registered but has no scenario in features/suites/.
test result: FAILED. 3 passed; 2 failed
```

Removed: the scenario was restored; five meta-gate tests pass.

### verify-examples can fail

Planted, first: the proof sentence of `examples/nat-add-zero/src/Main.lex.tex` changed to `Close the goal by reflexivity twice.`. Command: `cargo xtask verify-examples`. Expected: the example no longer passes the gate's first step.

```text
gate failed: nat-add-zero: fmt --check: LLF5005: not a registered proof sentence; the exact simple sentences are fixed
```

Planted, second (the record comparison itself, §29.5): the committed normalized verification record `examples/nat-add-zero/expected/verify/audit/output.txt` changed from `'LexLeanExample.Main.add_zero' does not depend on any axioms` to `'LexLeanExample.Main.add_zero' depends on axioms: [propext]`, so the source still verifies with real Lean 4.32.1 but its observed axiom audit no longer equals the committed record. Command: `cargo xtask verify-examples`. Expected: the example verifies, then the gate reports the drifted record after the examples that precede it alphabetically pass.

```text
verify-examples: list-induction verified (attestation 399964d863f7657b253d65d76eab32b26db86b7a7978f7f97a849ff8e66093ab)
verify-examples: list-induction: 7 normalized verification records equal expected/verify (§29.5)
verify-examples: nat-add-zero verified (attestation d614c14ebb6f5db3272cb6a1469309d046bf96931775e623c823c3c8ebf5a99a)
gate failed: R10: nat-add-zero: expected/verify/audit/output.txt differs from its committed oracle; a semantic change needs an explicit rewrite and review (§28.3)
```

Removed: the sentence and the record were restored; every example verifies with real Lean 4.32.1, prints its attestation ID, and its normalized records equal `expected/verify`.

### check-golden can fail

Planted: one byte appended to the committed oracle `examples/nat-add-zero/expected/build/modules/LexLeanExample/Main.lean`. Command: `cargo xtask check-golden`. Expected: the published build tree differs from the oracle (R10).

```text
gate failed: R10: nat-add-zero: expected/build/modules/LexLeanExample/Main.lean differs from its committed oracle; a semantic change needs an explicit rewrite and review (§28.3)
```

Removed: the oracle byte was restored; `check-golden` reports 6 published artifacts equal.

### check-reproducibility can fail

Planted: `publish_build` in `crates/lexlean/src/api.rs` made to write a `where.txt` containing the absolute project root into the staged build. Command: `cargo xtask check-reproducibility`. Expected: the two clean builds differ, or an absolute path is detected inside a published artifact (AR-07, AR-13).

```text
gate failed: AR-07: where.txt embeds the absolute checkout path /tmp/lexlean-build-VqKaW9
```

Removed: the write was deleted; the gate reports 6 published artifacts byte-identical across two directories.

### deny can fail

Planted: `walkdir = "2"` in the root `Cargo.toml` changed to `walkdir = "*"`. Command: `cargo deny --all-features check`. Expected: the wildcard ban fires (R6).

```text
error[wildcard]: found 2 wildcard dependencies for crate 'lexlean'
error[wildcard]: found 2 wildcard dependencies for crate 'repo-conformance'
error[wildcard]: found 1 wildcard dependency for crate 'xtask'
advisories ok, bans FAILED, licenses ok, sources ok
```

Removed: the requirement was restored; `cargo deny` reports every check ok.

### release-check can fail

Planted: a `release/` directory holding an SBOM `{"bomFormat":"CycloneDX","components":[]}` and a `checksums.txt` whose single line names `sbom.json` with an all-`f` digest, on the 0.1.0 tree. Command: `cargo xtask release-check`. Expected: the packaging round trip succeeds (it does: the packaged crate reports the same four-line identity), and every unmet §30.3/§30.4 criterion is listed by content, including the hash mismatch and the SBOM without the `lexlean` package.

```text
release-check: the packaged crate builds standalone with the same identity:
lexlean 0.1.0
language 1.0
compiler-semantics fe64624defc6e59ec80db231c0789c5fccdb926dcdad1dee47721b4961a425cf
lean-toolchain leanprover/lean4:v4.32.1

gate failed: RP-12: the release is refused; unmet criteria:
  source-tag: the workspace version is not 1.0.0; §2.3 fixes the first complete release at 1.0.0
  source-tag: CHANGELOG.md: No such file or directory (os error 2)
  checksums: sbom.json: hash mismatch
  host-binaries: release/bin/x86_64-unknown-linux-gnu/lexlean is missing or empty
  ...
  crate-package: release/lexlean.crate: No such file or directory (os error 2)
  semantics-id: release/compiler-semantics-id.txt is not one 64-hex-digit line
  version-output: release/version-output.txt: No such file or directory (os error 2)
  sbom: release/sbom.json does not list the lexlean package
  ci-evidence: release/vv-evidence.txt: No such file or directory (os error 2)
```

Removed: the planted `release/` directory was deleted. Refusal remains the honest state until 1.0.0; `conformance_rp_12` additionally builds a synthetic tree without release artifacts and asserts `checksums`, `sbom`, `crate-package`, and `version-output` are each reported unmet.

### check-fixtures can fail

Planted: the mutated word `banana` in `tests/negative/unknown-word/project/src/Main.lex.tex` changed to `cherry`, so the fixture's diagnostic message no longer equals its committed expectation. Command: `cargo xtask check-fixtures`. Expected: the fixture's `expected/command.json` differs from the observed run (§28.3).

```text
gate failed: <root>/tests/negative/unknown-word/expected/command.json differs from the observed run (§28.3: golden output changes only through `just fixtures-write`)
--- expected
{"artifacts":[],"command":"check","diagnostics":[{"causes":[],"code":"LLL1004","help":[],"labels":[],"message":"`banana` is not a declared atom in any visible glossary", ...
--- observed
{"artifacts":[],"command":"check","diagnostics":[{"causes":[],"code":"LLL1004","help":[],"labels":[],"message":"`cherry` is not a declared atom in any visible glossary", ...
```

Removed: the project file was restored; `check-fixtures` reports 33 fixtures equal to their expected files. `conformance_ex_07` runs the same comparison and additionally pins exactly one prescribed diagnostic code per §28.5 rejection class.

## End-to-end Lean evidence

The literal §29 example verifies against real `leanprover/lean4:v4.32.1`: probe elaboration, module compilation, separate-process `leanchecker` replay, exact `#print axioms` parsing, and the `\noaxioms` policy over an empty observed set (`conformance_ex_01`). The required §29.6 mutations are mechanized: a false proposition fails inside Lean and remaps to the source proof sentence (`conformance_ex_02`, `conformance_pf_18`); an undeclared title word fails lexical closure (`conformance_ex_03`); an indistinguishable same-surface entry is ambiguity, never priority (`conformance_ex_04`); an insufficient axiom allow-list fails policy checking with the observed excess recorded (`conformance_ex_05`, `conformance_vr_16`); and two clean builds in distinct paths publish byte-identical trees (`conformance_ex_06`, plus `just repro`).

The negative fixture suite (`tests/negative/<class>/`, §28.5) runs every rejection class through the CLI, including the Lean-backed ones: a Lean elaboration failure (`LLV7002`), a failing `leanchecker` (`LLV7003`, through a fixture toolchain overlay), malformed axiom output (`LLV7004`, through a `lake` overlay that corrupts only the audit run), an axiom-policy excess (`LLV7005`), a toolchain version mismatch (`LLV7001`), and a PDF executable hash mismatch (`LLS8004`). `conformance_vr_15` asserts that each failing stage (probe, module, replay, audit, policy) leaves no staging or verified directory behind, and `conformance_vr_07` plants a warning on a successful module compilation and asserts `LLV7006` with nothing published. `conformance_vr_10` runs the pinned `lean` on a module with three `#print axioms` commands and asserts the parser accepts the live output in the toolchain's own order and rejects an unknown-constant error line.
