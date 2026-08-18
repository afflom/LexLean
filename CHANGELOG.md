# Changelog

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and
the version axes are the ones SPEC.md §30.1 separates: the compiler crate and
binary carry the SemVer below, the language identifier is `1.0`, and the
compiler-semantics ID is a digest over the normative language data, schemas,
and pinned golden fixtures that `lexlean --version` prints.

SPEC.md §2.3 fixes `0.1.0` as the initial implementation version and `1.0.0` as
the first release satisfying the complete specification. A `0.1.0` tag is
therefore not a §30 release: `cargo xtask release-check` reads the complete
§30.3 artifact set and §30.4 completion criterion and refuses, naming every
criterion that does not hold. That refusal is the accurate answer at this
version, and the entry below says what the tag does and does not claim.

## 0.1.0

The initial implementation of `LEXLEAN-SPEC-1`.

### Implemented

All 210 conformance IDs of SPEC.md §31 are implemented at honesty level
`build`: constructed in this repository and validated against an oracle by the
test named `conformance_<id>`. [CONFORMANCE.md](CONFORMANCE.md) is the
generated register, [ERRORS.md](ERRORS.md) the closed diagnostic registry, and
[VERIFICATION.md](VERIFICATION.md) the falsifiability record for every gate.

- Closed project configuration, canonical lock file, and offline dependency
  policy (`CF-01`..`CF-15`).
- Total lexical closure over every accepted atom (`LX-01`..`LX-14`) and
  versioned lexicon packages with closed schemas, denotations, and renderer
  tokens (`GL-01`..`GL-16`).
- The fixed structural, mathematical, and proposition grammar with closed
  ambiguity handling (`GR-01`..`GR-16`), the typed closed IR with canonical
  serialization and content identities (`SM-01`..`SM-14`), and document
  definitions with exact self-application and acyclicity rules
  (`DF-01`..`DF-10`).
- The structured proof language with pinned Lean lowerings (`PF-01`..`PF-18`),
  prose-free deterministic generated Lean with complete token traceability
  (`LN-01`..`LN-12`), and canonical LaTeX regeneration with the optional
  hash-checked PDF provider (`TX-01`..`TX-12`).
- Canonical diagnostics, source maps, coverage, manifests, and reproducible
  builds (`AR-01`..`AR-14`); fifteen-stage verification with `leanchecker`
  replay and exact axiom audit (`VR-01`..`VR-18`); the exact CLI contract and
  the stable six-method Rust `Engine` API (`CL-01`..`CL-18`); filesystem
  confinement, no shell, no hidden network, and the closed failure model
  (`SE-01`..`SE-12`).
- Four example projects that verify under the pinned `leanprover/lean4:v4.32.1`
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
