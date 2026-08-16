# LexLean

A closed-lexicon LaTeX-to-Lean 4 compiler whose canonical document and prose-free Lean program are generated from one semantic representation.

The complete normative contract is [SPEC.md](SPEC.md) (`LEXLEAN-SPEC-1`). Every capability below is a claim in [`model/ids.toml`](model/ids.toml), carried at honesty level `build`: constructed here and validated against its oracle by the test named `conformance_<id>`. The generated register is [CONFORMANCE.md](CONFORMANCE.md); the closed diagnostic registry is [ERRORS.md](ERRORS.md); the falsifiability evidence is in [VERIFICATION.md](VERIFICATION.md).

## What it does

LexLean compiles `.lex.tex` modules written in a closed controlled language: every word, symbol, and control must be declared by a versioned lexicon package, every sentence parses under a fixed grammar, and one typed intermediate representation generates both the canonical LaTeX document and the prose-free Lean 4 program. Verification compiles the generated Lean under the pinned `leanprover/lean4:v4.32.1` toolchain, replays every module with `leanchecker`, audits axioms with exact `#print axioms` parsing, and publishes a content-addressed attestation.

```text
lexlean init --name my-doc --module-prefix MyDoc
lexlean lock
lexlean check
lexlean build
lexlean verify
```

## The literal example

[examples/nat-add-zero/src/Main.lex.tex](examples/nat-add-zero/src/Main.lex.tex) is the complete SPEC.md §29 document:

```latex
\begin{lexlean}{Main}
\useglossary{lexlean.std.nat@1.0.0}
\title{Natural number addition}

\begin{theorem}{add-zero}
\noaxioms
For every natural number \(n\), \(n + 0 = n\).
\begin{proof}
Close the goal by reflexivity.
\end{proof}
\end{theorem}
\end{lexlean}
```

From one linked representation it generates the prose-free Lean module

```lean
module
import Init
set_option autoImplicit false
namespace LexLeanExample.Main

public theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by
  rfl

end LexLeanExample.Main
```

and the canonical LaTeX document, regenerated from IR rather than copied ("The goal follows by reflexivity."), plus source maps, coverage, and a manifest — all byte-reproducible across directories. `lexlean verify` then compiles the module under the pinned toolchain, replays it with `leanchecker`, parses `#print axioms` exactly, and records the empty observed axiom set in a content-addressed attestation.

## Building and running the gate

Prerequisites: Rust 1.97 (`rust-toolchain.toml` pins it), [just](https://github.com/casey/just), `cargo-deny`, and the pinned Lean toolchain `leanprover/lean4:v4.32.1` installed through `elan` (the dev container in [.devcontainer/](.devcontainer/) provides all of them).

```text
just vv        # the complete normative acceptance gate (SPEC.md §9.2)
just release   # vv, then the §30 release criterion; refused until 1.0.0
```

All 209 registered conformance IDs are implemented and pass; `just vv` runs clean from a checkout with the pinned toolchain installed.

## Capabilities

Every row is validated by `just vv`; the IDs link the claim to its register row, scenario, and conformance test.

| Capability | IDs | Level |
| --- | --- | --- |
| Exact repository identity, layout, generated documents, and release gate | `RP-01`..`RP-12` | `build` |
| Closed project configuration, canonical lock file, and offline dependency policy | `CF-01`..`CF-15` | `build` |
| Total lexical closure: every accepted atom is covered by exactly one declared origin | `LX-01`..`LX-14` | `build` |
| Versioned lexicon packages with closed schemas, denotations, and renderer tokens | `GL-01`..`GL-16` | `build` |
| Fixed structural, mathematical, and proposition grammar with closed ambiguity handling | `GR-01`..`GR-16` | `build` |
| Typed closed IR with canonical serialization and content identities | `SM-01`..`SM-14` | `build` |
| Document definitions with exact self-application and acyclicity rules | `DF-01`..`DF-10` | `build` |
| The structured proof language with pinned Lean lowerings | `PF-01`..`PF-18` | `build` |
| Prose-free deterministic generated Lean with complete token traceability | `LN-01`..`LN-12` | `build` |
| Canonical LaTeX regeneration and the optional hash-checked PDF provider | `TX-01`..`TX-12` | `build` |
| Canonical diagnostics, source maps, coverage, manifests, and reproducible builds | `AR-01`..`AR-14` | `build` |
| Fifteen-stage verification with leanchecker replay and exact axiom audit | `VR-01`..`VR-18` | `build` |
| The exact CLI contract and the stable six-method Rust `Engine` API | `CL-01`..`CL-18` | `build` |
| Filesystem confinement, no shell, no hidden network, closed failure model | `SE-01`..`SE-12` | `build` |
| The literal `nat-add-zero` example and the complete negative fixture suite | `EX-01`..`EX-08` | `build` |

Range rows abbreviate consecutive registered IDs; every individual ID in each range is registered in [`model/ids.toml`](model/ids.toml) at the stated level with its own scenario and test.

## Evidence, not belief

- `check` and `build` never claim verification (`VR-18`); only `verify` runs Lean, and its attestation records toolchain hashes, process records, and observed axiom sets (`VR-01`..`VR-14`).
- Facts about external tools (Lean 4.32.1, Lake, leanchecker, `#print axioms` output shapes) are level `some-true` rows in [`model/ledger.toml`](model/ledger.toml): reproduced from cited authorities, not established here.
- The acceptance gate is `just vv` (SPEC.md §9.2); a release is refused until the complete §30 criterion holds (`RP-12`).

## Documented deviations

- Generated Lean declares `public theorem` / `public def` where SPEC.md §29.3 prints bare `theorem`: under the Lean 4.32.1 module system a non-`public` declaration is module-private, and the §18.9 axiom-audit module could not name it. The committed oracles carry `public`.
- The §21.5 `modules/<full-module-path>` artifact naming is realized as slash-separated directories (`modules/LexLeanExample/Main.lean`).
- Unique existence (§18.4 names `ExistsUnique`) lowers to its definitional expansion `Exists (fun (x : T) => And (P) ((y : T) → P[x:=y] → Eq y x))`: Lean 4.32.1's `Init` has no `ExistsUnique` constant. The linked IR keeps `ExistsUnique`; only the printed Lean bytes expand it, and a `Witness` step leaves the `And` goal for the remaining proof.
- The §18.8 probe module declares alpha-renamed universe variables with one `universe p0u ...` command before its `example` lines: Lean 4 has no `example.{u}` form.
- The pinned `leanchecker` has no version flag; its attestation `version_output` is the normalized answer to the fixed identity probe `lake env leanchecker LexLeanIdentityProbe`, checked against the pinned toolchain's exact response.

All are enforced by the same golden and conformance gates as everything else.

## Layout

Language data lives in [language/](language/), claim data in [model/](model/), schemas in [schemas/](schemas/), the compiler in [crates/lexlean/](crates/lexlean/), gates in [xtask/](xtask/) and [crates/conformance/](crates/conformance/), the literal example in [examples/nat-add-zero/](examples/nat-add-zero/), and the negative fixtures in [tests/negative/](tests/negative/).

## License

Dual-licensed under [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
