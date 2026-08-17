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

## Install

`lexlean verify` runs the pinned `leanprover/lean4:v4.32.1` toolchain, so the
published container image carries both and is the shortest path to a run that
can actually verify:

```text
docker pull ghcr.io/afflom/lexlean:0.1.0
docker run --rm -v "$PWD:/work" ghcr.io/afflom/lexlean:0.1.0 verify
```

The image is around 4 GB, nearly all of it the pinned toolchain's compiled
library — the part `verify` needs and the part a smaller image would have to
leave out.

Each [release](https://github.com/afflom/lexlean/releases) also attaches one
binary per supported host (SPEC.md §8.3), the packaged crate, a CycloneDX bill
of materials, `checksums.txt` over every other asset, and the `just vv`
evidence for the tagged commit. A binary alone can `init`, `lock`, `fmt`,
`check`, and `build`; `verify` additionally needs the pinned toolchain
installed through [elan](https://github.com/leanprover/elan).

From source, with the prerequisites below:

```text
cargo install --locked --path crates/lexlean
```

Versions follow SPEC.md §30.1 and are recorded in [CHANGELOG.md](CHANGELOG.md).
§2.3 fixes `0.1.0` as the initial implementation version and `1.0.0` as the
first release satisfying the complete specification, so a `0.1.0` tag does not
claim the §30 release criterion — `cargo xtask release-check` reads that
criterion and says exactly which parts of it do not yet hold.

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
public import Init
set_option autoImplicit false
namespace LexLeanExample.Main

public theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by
  rfl

end LexLeanExample.Main
```

and the canonical LaTeX document, regenerated from IR rather than copied ("The goal follows by reflexivity."), plus source maps, coverage, and a manifest — all byte-reproducible across directories. `lexlean verify` then compiles the module under the pinned toolchain, replays it with `leanchecker`, parses `#print axioms` exactly, and records the empty observed axiom set in a content-addressed attestation.

## Examples that verify under the pinned toolchain

Every directory under [examples/](examples/) is discovered by the example gate (`EX-08`) and must format, lock, check, build, and verify with real Lean 4.32.1 (`cargo xtask verify-examples`). Its platform-independent build outputs and its normalized verification records are committed under `expected/` and compared byte for byte by the golden gate (§28.3) and the example gate (§29.5); that those bytes are also independent of where the build ran is the separate claim of `AR-13` and `EX-06`.

| Example | What it exercises |
| --- | --- |
| [nat-add-zero](examples/nat-add-zero/) | The literal SPEC.md §29 document (`EX-01`..`EX-06`). |
| [peano-arithmetic](examples/peano-arithmetic/) | Five modules with explicit imports, a local path glossary of proof constants from `Init` (`Nat.add_comm`, `Nat.le_trans`, `Eq.symm`, universe-polymorphic `rfl`, ...), label words, document-denoted definitions of all three kinds (`count`, `double`, `even`, `positive`, `divides`), noun-of and binary-noun-of frames (`the successor of`, `the sum of ... and ...`), sections with inherited parameters and references to parameterized declarations, and every §16 proof form: `Assume`, `Apply`, `Close the goal with`/`by reflexivity`, witnesses, left/right, multi-rule `rewrite` at the goal, `constructor`, `cases` on naturals and on hypotheses (`And`, `Exists`), `induction`, and `calculate`; theorems under `\noaxioms`, `\allowaxioms{propext}`, and `\exactaxioms{Classical.choice;Quot.sound;propext}` whose observed axiom sets are audited exactly. |
| [propositional-logic](examples/propositional-logic/) | Reasoning over `Prop`-typed locals with a `proposition` type noun defined as the sort: commutativity and associativity of conjunction and disjunction, disjunction elimination, double negation, De Morgan, explosion, biconditionals, and classical double-negation elimination under an exact axiom policy — through cases on `And`/`Or`/`Iff` hypotheses, `constructor`, and `Apply`. |
| [list-induction](examples/list-induction/) | Universe-polymorphic `List` with an eliminator descriptor: type-valued section parameters, `List.nil`/`List.cons`, an infix `⧺` for `List.append`, structural induction over lists using earlier document lemmas as rewrite rules, and nested noun phrases (`the length of ... equals the sum of the length of ... and the length of ...`). |

## Building and running the gate

Prerequisites: Rust 1.97 (`rust-toolchain.toml` pins it), [just](https://github.com/casey/just), `cargo-deny`, and the pinned Lean toolchain `leanprover/lean4:v4.32.1` installed through `elan` (the dev container in [.devcontainer/](.devcontainer/) provides all of them).

```text
just vv        # the complete normative acceptance gate (SPEC.md §9.2)
just release   # vv, then the §30 release criterion; refused until 1.0.0
```

All 209 registered conformance IDs are implemented and pass; `just vv` runs clean from a checkout with the pinned toolchain installed.

`just vv` is the Linux x86-64 gate. On the other four supported hosts (§8.3) the crate builds and every test runs. A case whose assertions need something the host does not have runs its platform-independent assertions and prints which ones it skipped: the pinned toolchain, a `#!/bin/sh` program for the external-provider cases, a filesystem that distinguishes two names differing only in case, or one that accepts a name that is not valid UTF-8. Each is detected at run time rather than assumed from the target triple, and on Linux x86-64 the toolchain gate is mandatory, so nothing there passes vacuously.

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
| The literal `nat-add-zero` example, the Lean-verified feature examples, and the complete negative fixture suite | `EX-01`..`EX-08` | `build` |

Range rows abbreviate consecutive registered IDs; every individual ID in each range is registered in [`model/ids.toml`](model/ids.toml) at the stated level with its own scenario and test.

## Evidence, not belief

- `check` and `build` never claim verification (`VR-18`); only `verify` runs Lean, and its attestation records toolchain hashes, process records, and observed axiom sets (`VR-01`..`VR-14`).
- Facts about external tools (Lean 4.32.1, Lake, leanchecker, `#print axioms` output shapes) are level `some-true` rows in [`model/ledger.toml`](model/ledger.toml): reproduced from cited authorities, not established here.
- The acceptance gate is `just vv` (SPEC.md §9.2); a release is refused until the complete §30 criterion holds (`RP-12`).

## Documented deviations

- Generated Lean declares `public theorem` / `@[expose] public def` and `public import` where SPEC.md §18.1/§29.3 print bare `theorem` and `import`: under the Lean 4.32.1 module system a non-`public` declaration is module-private (the §18.9 axiom-audit module could not name it), and a non-`public` import may not contribute constants to a public declaration's signature, and a definition body is hidden from importing modules unless exposed (a theorem in another module could not unfold or eliminate a document definition). The committed oracles carry `public`.
- The §21.5 `modules/<full-module-path>` artifact naming is realized as slash-separated directories (`modules/LexLeanExample/Main.lean`).
- Unique existence (§18.4 names `ExistsUnique`) lowers to its definitional expansion `Exists (fun (x : T) => And (P) ((y : T) → P[x:=y] → Eq y x))`: Lean 4.32.1's `Init` has no `ExistsUnique` constant. The linked IR keeps `ExistsUnique`; only the printed Lean bytes expand it, and a `Witness` step leaves the `And` goal for the remaining proof.
- The §18.8 probe module declares alpha-renamed universe variables with one `universe p0u ...` command before its `example` lines: Lean 4 has no `example.{u}` form.
- The pinned `leanchecker` has no version flag; its attestation `version_output` is the normalized answer to the fixed identity probe `lake env <leanchecker> LexLeanIdentityProbe` (the preflighted executable by absolute path), checked against the pinned toolchain's exact response.
- §23.5's "two spaces per environment nesting level" is realized as two spaces per *section* depth: the §29.2 literal indents nothing inside `theorem` or `proof`, so declaration and proof environments do not add a level; only `\begin{section}` nesting does (`LX-14`, and every example's committed source is `fmt --check` clean).
- A numeral with a redundant leading zero (`007`) is rejected as noncanonical decimal source (`LLL1003`, with the canonical spelling as help) although §12's lexical class admits any digit run: canonical source has one spelling per value, and the formatter cannot choose between two.
- §18.4 says generated numerals carry an expected type, and the §29.3 literal prints `Nat.add llv0 0` bare. Generated Lean prints a numeral bare exactly where the applied signature binder is a monomorphic constant type and ascribes it (`(0 : Nat)`) everywhere else, so the literal and the rule agree. The ascription is what a document type definition is *defined as*, in whichever module of the project declares it (§17.7), never the definition's own name: Lean's `OfNat` instances live on the underlying type.
- §20.4's fallback for a Lean diagnostic that no generated mapping encloses ("the declaration component") is realized as the nearest preceding declaration-role mapping of the generated module: a location after the last declaration (the closing `end`) remaps to that last declaration, with the unmapped generated range kept as a note.
- Fixture directories are named `tests/fixtures/<suite>/<id>-<slug>/` and `tests/negative/<class>/` (`cl-04-check-no-artifacts`, `vr-11-exact-mismatch`) where §28.2 writes `tests/fixtures/<suite>/<id>/`: one ID may own several fixtures, and the slug names which; the runner discovers fixtures by their `case.toml`, never by directory name, and every fixture runs from a temporary copy of its committed `project/`.
- A nested proof scope — a `constructor` branch, an `apply` premise, a `cases`/`induction` case — is set inside a `quote` environment. §19.5 fixes the phrases, not the layout, and a flat rendering makes two proofs that differ only in how their branches nest render to the same bytes; the indentation says where each scope closes, so the document presents the proof IR faithfully (§6 I8).
- Canonical LaTeX renders a quantified proposition as prose only in trailing position (the source formatter's §15.6 rule); a quantified operand that must be an island states its binder types (`\exists m \in \mathbb{N}, ...`), which the source math grammar has no spelling for. Document references no visible entry names render as `\texttt{Module::component}`, the escape form of qualified selectors, under their own coverage origin.
- Every identifier-shaped name canonical LaTeX emits --- a display spelling or math identifier (§12.2 admits `_` and `'`), a module segment (§15.1 admits `_`), an LRE operator name (§13.9 admits `_`), a glossary surface --- is emitted through the registered `\_` token wherever it carries `_`, which TeX would otherwise read as a subscript. The escape carries its own renderer-token coverage origin and the runs around it keep the name's, so §19.6 output coverage stays exact.
- §13.5 rule 5 admits a non-ASCII scalar in a canonical *source* form, but the canonical document emits glyphs only through the renderer-token registry (§19.1, §13.10), which the fixed §19.2 preamble can typeset. An entry whose LRE renders such a surface directly instead of naming a token is refused with `LLB6002` naming the entry, the form, and the scalar; every shipped core and standard entry with a Unicode surface already names one.
- §17.8 fixes generated local names as `llv<n>` / `llh<n>` in introduction order. A binder that the generated declaration never references keeps its index and carries a `_` prefix (`_llv1`, `_llh0`): pinned Lean's `unusedVariables` linter warns about an unreferenced binding, §20.2 makes any Lean warning a verification failure, and §18.1 fixes the file structure so no `set_option` may silence it — without the prefix an ordinary proposition with an unused quantified binder (`For every natural number \(n\) and natural number \(m\), \(n + 0 = n\)`) could never verify. The prefix marks the binding as deliberate; nothing else changes.

All are enforced by the same golden and conformance gates as everything else.

## Layout

Language data lives in [language/](language/), claim data in [model/](model/), schemas in [schemas/](schemas/), the compiler in [crates/lexlean/](crates/lexlean/), gates in [xtask/](xtask/) and [crates/conformance/](crates/conformance/), the examples in [examples/](examples/), and the negative fixtures in [tests/negative/](tests/negative/).

## License

Dual-licensed under [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
