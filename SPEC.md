# LexLean Repository and Project Specification

**Repository:** `https://github.com/afflom/lexlean`  
**Project name:** LexLean  
**Rust crate and executable:** `lexlean`  
**Specification identifier:** `LEXLEAN-SPEC-1`  
**Language identifier:** `lexlean-language/1.0`  
**Project-schema identifier:** `lexlean/project/1`  
**Status:** Normative implementation specification  
**Target initial release:** `1.0.0`

---

## 1. Normative force

This document is the complete implementation contract for `github.com/afflom/lexlean`.

The key words **MUST**, **MUST NOT**, **REQUIRED**, **SHALL**, **SHALL NOT**, **SHOULD**, **SHOULD NOT**, and **MAY** are normative. A behavior not authorized by this specification is not part of LexLean 1.0.

A LexLean implementation conforms to this specification only when:

1. every conformance ID in §31 is present in `model/ids.toml` at honesty level `build`;
2. every ID has exactly one scenario in its named `features/suites/*.feature` file;
3. every ID has exactly one Rust conformance test named `conformance_<id>`, where hyphens are changed to underscores and letters are lower-case;
4. every required positive and negative fixture passes;
5. `just vv` succeeds from a clean checkout;
6. all generated platform-independent artifacts match their committed oracles;
7. every verification fixture passes with the pinned Lean toolchain;
8. no public capability is represented as complete while any required branch, error path, artifact, or audit remains absent.

The repository MUST NOT ship a partial implementation under the LexLean 1.0 language identifier. Work may occur on branches with failing tests, but the default branch and every release tag MUST satisfy the entire acceptance gate.

---

## 2. Repository identity and initialization

### 2.1 Name

The repository name is **LexLean** and its canonical GitHub location is:

```text
https://github.com/afflom/lexlean
```

The Cargo package, library crate, and executable are all named `lexlean`.

The one-line description is:

> A closed-lexicon LaTeX-to-Lean 4 compiler whose canonical document and prose-free Lean program are generated from one semantic representation.

### 2.2 Template origin

The repository MUST be created from `UOR-Foundation/template`, using template commit:

```text
0a1c799338d7db829aa23365e1acf4f9d01ff8b5
```

The inherited claim model, conformance runner, falsifiable gate discipline, dual license, and `xtask` pattern MUST be retained. Domain-specific remnants from the repository from which the template was cut MUST be removed or rewritten; in particular, the inherited `audit-limits` allow-list is not applicable to LexLean.

### 2.3 Repository metadata

The root workspace metadata MUST be:

```toml
[workspace.package]
version = "0.1.1"
edition = "2021"
rust-version = "1.97"
license = "MIT OR Apache-2.0"
repository = "https://github.com/afflom/lexlean"
homepage = "https://github.com/afflom/lexlean"
authors = ["Alex Flom"]
keywords = ["lean", "latex", "formal-methods", "compiler", "proof"]
categories = ["compilers", "development-tools"]
```

The initial implementation version is `0.1.0`. The first release satisfying this complete specification is `1.0.0`.

### 2.4 License

The repository MUST remain dual-licensed under:

- Apache License 2.0; or
- MIT;

at the recipient's option. `LICENSE-APACHE` and `LICENSE-MIT` MUST remain at the repository root.

---

## 3. Purpose

LexLean compiles a closed, glossary-defined mathematical document language with a LaTeX surface into:

1. a typed semantic intermediate representation;
2. canonical human-readable LaTeX;
3. prose-free Lean 4 source;
4. source maps and complete lexical-coverage records;
5. deterministic build manifests; and
6. verification attestations produced only after Lean elaboration, kernel replay, and axiom-policy checking succeed.

The central property is:

> No accepted LexLean document contains an uninterpreted word, symbol, punctuation mark, control sequence, reference, or semantically relevant structural token.

The document is a program. Human-visible mathematical text and kernel-visible Lean declarations are two renderings of one linked semantic object.

---

## 4. Scope and non-goals

### 4.1 LexLean 1.0 supports

LexLean 1.0 MUST support:

- closed lexical resolution for all source tokens;
- a fixed controlled grammar for propositions and definitional statements;
- symbolic mathematical expressions with glossary-defined operators;
- document modules and explicit module imports;
- glossary packages and exact package locking;
- scoped section parameters, quantified binders, proof locals, and branch locals;
- nonrecursive type aliases, term definitions, and predicate definitions;
- theorem, lemma, and corollary declarations;
- structured proofs using the proof forms in §14;
- external Lean constants with declared LexLean signatures;
- canonical LaTeX rendering from the semantic IR;
- Lean 4 generation with no comments, strings, documentation text, or proof holes;
- verification in a pinned Lake workspace;
- per-declaration axiom-dependency policies;
- optional isolated PDF rendering through the external-provider protocol in §19;
- human and canonical-JSON diagnostics;
- a Rust library API and command-line interface;
- deterministic, content-addressed build artifacts.

### 4.2 LexLean 1.0 deliberately does not support

The following are outside the LexLean 1.0 language and MUST be rejected rather than approximated:

- arbitrary natural language;
- unrestricted LaTeX;
- TeX macro definition or macro expansion;
- raw Lean declarations, terms, tactics, commands, or code blocks;
- source comments of any kind;
- free expository paragraphs;
- author-defined axioms;
- `sorry`, `admit`, synthetic proof placeholders, or deferred proof nodes;
- recursive or mutually recursive document definitions;
- document-defined inductive types, structures, classes, or instances;
- string literals, file inclusion, shell escape, network access, or foreign code;
- heuristic ambiguity resolution;
- probabilistic or model-based translation;
- a claim that `leanchecker` is an independent proof checker;
- a claim that successful Rust generation alone establishes a theorem;
- a claim that imported libraries are proved by LexLean.

Complex Lean objects that LexLean 1.0 cannot define MAY be imported as closed external glossary entries. Their guarantees belong to their upstream repositories. LexLean verifies only that the generated declarations elaborate and check in the pinned environment and that their observed axiom dependencies satisfy their explicit policies.

---

## 5. Trust and evidence model

### 5.1 Trusted computing base

A verification attestation depends on:

1. the exact LexLean compiler semantics identified in the build manifest;
2. the pinned Lean 4 toolchain;
3. Lean's elaborator and kernel;
4. the `leanchecker` executable from that same toolchain, used as a separate-process replay check;
5. the imported Lean workspace and its locked dependencies;
6. the operating system, filesystem, and process implementation;
7. any external PDF engine only for PDF bytes, never for theorem verification.

### 5.2 Untrusted inputs

LexLean MUST treat all of the following as untrusted:

- `.lex.tex` source;
- project configuration;
- lock files;
- glossary packages;
- imported path-package contents;
- external tool output;
- existing build directories;
- generated files from previous runs.

Every untrusted input MUST be parsed, validated, bounded by the project's explicit resource policy, and either accepted under a specified schema or rejected.

### 5.3 Evidence states

LexLean distinguishes:

- **checked**: lexical, grammatical, resolution, linking, and LexLean semantic checks succeeded;
- **built**: checked, and canonical artifacts were emitted;
- **verified**: built, Lean elaboration succeeded, `leanchecker` replay succeeded, the axiom audit succeeded, and every declaration satisfied its policy.

The words “proved”, “verified”, “kernel-checked”, and equivalent status markers MUST NOT be emitted for a merely checked or built result.

### 5.4 Axiom audit scope

LexLean's axiom audit is specifically an **axiom-dependency** audit. It reports the transitive axioms returned by Lean's `#print axioms`. It is not a general dependency graph, a source provenance proof, or an independent semantic interpretation of imported code.

---

## 6. Global invariants

Every implementation path MUST preserve all of the following.

### I1. Lexical closure

Every accepted non-whitespace source atom is covered exactly once by a selected glossary entry, a core structural entry, a numeric constructor, or a scoped declaration.

### I2. Symbol closure

Mathematical symbols, punctuation, braces, delimiters, control sequences, and reference syntax are subject to the same closure requirement as prose words.

### I3. Grammatical closure

A sequence of known lexical items is not sufficient. The complete component MUST parse under the versioned controlled grammar.

### I4. Semantic closure

Every accepted parse constructs a defined semantic IR node. There is no opaque “text” node.

### I5. Unique interpretation

After lexical alternatives, parses, name resolution, and type-directed filtering are considered, exactly one distinct linked IR is required. Zero interpretations is an error. More than one distinct interpretation is an ambiguity error. LexLean MUST NOT guess.

### I6. No bypass

There is no raw-LaTeX, raw-Lean, raw-tactic, raw-HTML, raw-string, or untyped extension escape.

### I7. Single semantic source

Canonical LaTeX and Lean source are generated from the same linked IR. Neither generated artifact is parsed to create the other.

### I8. Canonical publication

The publishable mathematical document is the canonical LaTeX renderer's output, not the author's unchecked source bytes.

### I9. Scoped declarations

Every variable or hypothesis occurrence resolves to a unique scoped declaration. Capture is prevented by internal IDs, not spelling conventions.

### I10. Determinism

Given identical normalized source, project configuration, lock file, glossary closure, compiler-semantics identifier, and Lean toolchain identifier, platform-independent outputs are byte-identical.

### I11. Verification honesty

No verified attestation exists unless every required verification stage succeeds. A failed stage removes the staging directory and produces no verified directory.

### I12. No hidden proof assumptions

Every emitted declaration has an explicit axiom policy, and the observed set is recorded.

### I13. Complete traceability

Every semantic token in generated Lean and every visible token or control sequence in canonical LaTeX traces to an IR node and ultimately to source, glossary, or compiler-prelude origin.

### I14. Closed failure model

Every user-visible failure has a registered diagnostic code and a sanctioned exit-code class. User-controlled input MUST NOT cause a panic.

### I15. Offline verification

`check`, `build`, `fmt`, and `verify` perform no network operation. Package acquisition is confined to an explicit `lock --allow-network` invocation.

---

## 7. Repository layout

The completed repository MUST have this layout. Additional files are allowed only when they have a defined role and are included by the repository audits.

```text
.
├── .cargo/
│   └── config.toml
├── .devcontainer/
│   └── devcontainer.json
├── .github/
│   └── workflows/
│       ├── ci.yml
│       ├── honesty.yml
│       └── reproducibility.yml
├── AGENTS.md
├── CONFORMANCE.md
├── ERRORS.md
├── README.md
├── SPEC.md
├── VERIFICATION.md
├── Cargo.lock
├── Cargo.toml
├── Justfile
├── LICENSE-APACHE
├── LICENSE-MIT
├── clippy.toml
├── deny.toml
├── lean-toolchain
├── rust-toolchain.toml
├── rustfmt.toml
├── crates/
│   ├── lexlean/
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── api.rs
│   │       ├── artifact/
│   │       │   ├── canonical_json.rs
│   │       │   ├── content_id.rs
│   │       │   ├── manifest.rs
│   │       │   ├── mod.rs
│   │       │   └── source_map.rs
│   │       ├── backend/
│   │       │   ├── latex.rs
│   │       │   ├── lean.rs
│   │       │   ├── mod.rs
│   │       │   └── pdf.rs
│   │       ├── cli.rs
│   │       ├── config.rs
│   │       ├── diagnostic.rs
│   │       ├── elaborate/
│   │       │   ├── definitions.rs
│   │       │   ├── expressions.rs
│   │       │   ├── mod.rs
│   │       │   ├── proofs.rs
│   │       │   └── resolve.rs
│   │       ├── error.rs
│   │       ├── fmt.rs
│   │       ├── grammar/
│   │       │   ├── chart.rs
│   │       │   ├── math.rs
│   │       │   ├── mod.rs
│   │       │   ├── proposition.rs
│   │       │   ├── proof.rs
│   │       │   └── structural.rs
│   │       ├── ir/
│   │       │   ├── declaration.rs
│   │       │   ├── document.rs
│   │       │   ├── mod.rs
│   │       │   ├── proof.rs
│   │       │   └── term.rs
│   │       ├── lexicon/
│   │       │   ├── entry.rs
│   │       │   ├── lre.rs
│   │       │   ├── lse.rs
│   │       │   ├── mod.rs
│   │       │   ├── package.rs
│   │       │   └── resolve.rs
│   │       ├── lib.rs
│   │       ├── link.rs
│   │       ├── lock.rs
│   │       ├── main.rs
│   │       ├── project.rs
│   │       ├── source/
│   │       │   ├── atom.rs
│   │       │   ├── coverage.rs
│   │       │   ├── mod.rs
│   │       │   ├── normalize.rs
│   │       │   └── scan.rs
│   │       └── verify/
│   │           ├── axiom.rs
│   │           ├── child.rs
│   │           ├── leanchecker.rs
│   │           ├── mod.rs
│   │           ├── toolchain.rs
│   │           └── workspace.rs
│   ├── model/
│   └── conformance/
├── examples/
│   └── nat-add-zero/
├── features/
│   └── suites/
├── language/
│   ├── bootstrap.toml
│   ├── semantics.toml
│   ├── renderer-tokens.toml
│   ├── core/
│   │   ├── lexicon.toml
│   │   └── entries/
│   └── std/
│       └── nat/
│           ├── lexicon.toml
│           └── entries/
├── model/
│   ├── authorities.toml
│   ├── errors.toml
│   ├── ids.toml
│   └── ledger.toml
├── schemas/
│   ├── attestation.schema.json
│   ├── build-manifest.schema.json
│   ├── coverage.schema.json
│   ├── diagnostic.schema.json
│   ├── entry.schema.json
│   ├── lexicon.schema.json
│   ├── lock.schema.json
│   ├── project.schema.json
│   └── source-map.schema.json
├── tests/
│   ├── fixtures/
│   ├── golden/
│   └── negative/
└── xtask/
    ├── Cargo.toml
    └── src/
        ├── audit.rs
        ├── codegen.rs
        ├── main.rs
        └── spec_links.rs
```

`CONFORMANCE.md` and `ERRORS.md` are generated and committed. Their committed bytes MUST equal regeneration from `model/*.toml`.

`language/` is the compiler's versioned built-in language data. It is distinct from `model/`, which records claims about the repository.

---

## 8. Toolchains, platforms, and dependency policy

### 8.1 Rust

The exact repository Rust toolchain is:

```toml
[toolchain]
channel = "1.97.1"
components = ["rustfmt", "clippy"]
profile = "minimal"
```

The workspace uses Rust edition 2021 and MSRV 1.97. The shipped crate MUST compile with `#![forbid(unsafe_code)]`.

### 8.2 Lean

LexLean language 1.0 is pinned to:

```text
leanprover/lean4:v4.32.1
```

The repository-root `lean-toolchain` file MUST contain exactly that line followed by LF.

The corresponding Lean tag resolves to source commit:

```text
f054605aea4b840552cca2e725580bffd1e1b704
```

LexLean MUST reject a verification environment whose reported Lean version is not 4.32.1. The verification attestation records the SHA-256 digest of the actual `lean`, `lake`, and `leanchecker` executables used, so platform-specific executable bytes do not need to be assumed identical.

### 8.3 Supported hosts

The Rust crate MUST build and its non-Lean tests MUST pass on:

- Linux x86-64;
- Linux AArch64;
- macOS x86-64;
- macOS AArch64;
- Windows x86-64.

The normative full verification and reproducibility gate runs on Linux x86-64. Other hosts produce platform-bound attestations and MUST obey the same source, manifest, and policy formats.

Non-UTF-8 project paths are outside language 1.0 and produce a registered environment diagnostic.

### 8.4 Cargo dependency rules

- Every dependency requirement MUST be explicit; wildcard requirements are forbidden.
- `Cargo.lock` is committed.
- `cargo deny --all-features check` is part of `just vv`.
- Unknown registries and unknown Git sources are denied.
- `repo-model`, `repo-conformance`, and `xtask` are `publish = false`.
- No shipped crate may depend on a `publish = false` repository crate.
- Cargo features MUST NOT disable a normative capability. LexLean 1.0 defines no optional capability feature.
- Dependency additions require a license decision and an update to `deny.toml` only when the actual graph requires it.

### 8.5 Required implementation dependencies

The implementation MAY choose exact compatible releases through `Cargo.lock`, but the dependency roles are fixed:

- CLI parsing;
- TOML parsing;
- JSON parsing and serialization;
- SHA-256;
- semantic-version parsing;
- UTF-8 path handling;
- Unicode NFC normalization;
- structured errors;
- temporary directories;
- directory walking;
- file locking.

No dependency may provide arbitrary TeX execution, Lean parsing by string substitution, probabilistic language interpretation, or a second proof authority.

---

## 9. Root tooling

### 9.1 `.cargo/config.toml`

The file MUST contain only repository aliases; target-specific remnants from the template MUST be removed.

```toml
[alias]
xtask = "run --package xtask --"
vv = "run --package xtask -- validate"
```

### 9.2 `Justfile`

The normative acceptance recipe is `just vv`. It MUST run, in this order:

1. `fmt-check`;
2. `model`;
3. `spec-links`;
4. `lint`;
5. `test`;
6. `features`;
7. `bdd`;
8. `examples`;
9. `golden`;
10. `repro`;
11. `deny`.

The recipes have these meanings:

```text
fmt-check   cargo fmt --all -- --check
model       cargo xtask validate-model
spec-links  cargo xtask validate-spec-links
lint        cargo clippy --workspace --all-targets --all-features -- -D warnings
test        cargo test --workspace --all-features
features    cargo check --workspace --all-features --all-targets
bdd         cargo test -p repo-conformance
examples    cargo xtask verify-examples
golden      cargo xtask check-golden
repro       cargo xtask check-reproducibility
deny        cargo deny --all-features check
vv          all recipes above, in order
```

`just model-write` regenerates `CONFORMANCE.md` and `ERRORS.md`. Golden files are rewritten only by the explicit `just golden-write` recipe. No acceptance recipe rewrites source or expected output.

### 9.3 Development container

The development container MUST install:

- Rust 1.97.1 with `rustfmt` and `clippy`;
- `just`;
- `cargo-deny`;
- `elan`;
- `leanprover/lean4:v4.32.1`;
- the Rust Analyzer and Lean 4 editor extensions.

Its post-create command MUST install the pinned Lean toolchain explicitly and MUST NOT select an unpinned default. The container configuration is development support; verification still performs its own version and digest preflight.

### 9.4 Continuous integration

`ci.yml` MUST run `just vv` from a clean checkout on Linux x86-64. It MUST install the exact Rust toolchain, Lean 4.32.1 through `elan`, `just`, and `cargo-deny`.

`honesty.yml` MUST run the model/honesty gate separately so claim drift is distinguishable from code failure.

`reproducibility.yml` MUST perform two builds in distinct absolute directories and compare every platform-independent artifact byte-for-byte after path normalization.

---

## 10. Project files

A LexLean project contains:

- one `lexlean.toml`;
- one generated `lexlean.lock`;
- one `lean-toolchain`;
- a valid Lake workspace;
- one or more `.lex.tex` modules under configured source roots;
- zero or more local lexicon packages;
- `.lexlean/`, reserved for generated and verified artifacts.

No project file may override the language grammar, backend, verifier sequence, axiom-audit parser, source-map format, or verified artifact set.

### 10.1 `lexlean.toml`

`lexlean.toml` is UTF-8, NFC, LF-terminated TOML. Comments are forbidden. Unknown fields are errors. Every field below is required except `[pdf]`.

```toml
spec = "lexlean/project/1"
name = "example-project"
language = "1.0"
module_prefix = "ExampleProject"
source_roots = ["src"]
entrypoints = ["src/Main.lex.tex"]
build_root = ".lexlean"
lockfile = "lexlean.lock"
lean_workspace = "."
lean_toolchain = "leanprover/lean4:v4.32.1"

[[lexicon_source]]
package = "lexlean.std.nat"
kind = "builtin"

[limits]
max_file_bytes = 4194304
max_total_source_bytes = 67108864
max_primitive_atoms = 2000000
max_token_lattice_edges = 4000000
max_parse_states = 4000000
max_ir_nodes = 2000000
max_scope_depth = 1024
max_import_depth = 128
max_diagnostics = 256
max_child_output_bytes = 16777216
child_timeout_ms = 300000
```

#### Canonical project serialization

The parsed project has one canonical TOML serialization used by `project_config_sha256` and `source_id`. It writes:

1. scalar top-level keys in the order shown by the schema example;
2. `lexicon_source` tables sorted by `package`, with keys in the order `package`, `kind`, then kind-specific fields;
3. `[limits]` with keys in the order shown;
4. optional `[pdf]` last, with keys in the order shown;
5. basic quoted strings, decimal integers, arrays with comma-space separators, LF line endings, and one final LF;
6. no comments, blank leading lines, or trailing spaces.

Input whitespace does not affect this canonical serialization. A project may be semantically valid before formatting, but `lexlean lock --check` and repository examples require canonical bytes.

#### Project-field rules

| Field | Rule |
|---|---|
| `spec` | Exactly `lexlean/project/1`. |
| `name` | Lower-case ASCII package identifier: `[a-z][a-z0-9-]{0,62}`. |
| `language` | Exactly `1.0`. |
| `module_prefix` | One or more dot-separated ASCII Lean-name segments matching `[A-Z][A-Za-z0-9_]*`. |
| `source_roots` | Nonempty, unique, sorted project-relative directories. |
| `entrypoints` | Nonempty, unique, sorted project-relative `.lex.tex` files beneath a source root. |
| `build_root` | Project-relative directory; must resolve within the project and must not be a symlink. |
| `lockfile` | Project-relative regular-file path; exactly one lock file. |
| `lean_workspace` | Project-relative directory containing `lean-toolchain` and a Lake configuration. |
| `lean_toolchain` | Exactly the language-1.0 toolchain string. |
| `lexicon_source` | Unique by package and sorted by package identifier. |
| `limits` | Every listed positive integer is required. There are no hidden compiler defaults. |

#### Lexicon-source forms

A source is exactly one of:

```toml
[[lexicon_source]]
package = "lexlean.std.nat"
kind = "builtin"
```

```toml
[[lexicon_source]]
package = "example.algebra"
kind = "path"
path = "glossary/example.algebra"
```

```toml
[[lexicon_source]]
package = "example.algebra"
kind = "git"
url = "https://github.com/example/algebra-lexicon.git"
revision = "0123456789abcdef0123456789abcdef01234567"
subdirectory = "lexicon"
```

Rules:

- `builtin` accepts no additional fields.
- `path` requires `path` and accepts no URL or revision.
- `git` requires HTTPS URL, exact 40-lowercase-hex commit, and a relative `subdirectory`; it accepts no branch, tag, or mutable reference.
- package IDs match `[a-z][a-z0-9]*(\.[a-z][a-z0-9-]*)*`.
- source order does not create shadowing.
- path packages and cached Git packages are hashed as described in §21.4.
- `check`, `build`, `fmt`, and `verify` never fetch a missing Git source.

### 10.2 Explicit resource policy

The values under `[limits]` are semantic inputs to acceptance. `max_total_source_bytes` counts normalized selected modules, loaded lexicon manifests and entries, configuration, and lock bytes. Exceeding one produces `LLS8002` and identifies:

- the limit name;
- configured value;
- observed value, when safely known;
- the source or phase involved.

The compiler MUST stream or incrementally inspect configuration and lock data so that it does not require a hidden pre-configuration size limit. Platform allocation failure is reported as an environment failure, not misrepresented as a language error.

### 10.3 Optional PDF provider

When `[pdf]` is absent, no PDF is requested or emitted. When present, all fields are required:

```toml
[pdf]
mode = "external"
program = "tools/tectonic"
program_sha256 = "64-lowercase-hex-digits"
version_argv = ["--version"]
version_stdout_sha256 = "64-lowercase-hex-digits"
compile_argv = ["--outdir", "{out_dir}", "{input}"]
output = "{stem}.pdf"
resources = []
```

Only `mode = "external"` exists in language 1.0. The protocol is specified in §19.

### 10.4 Lake workspace pin

The project `lean-toolchain` MUST contain the exact toolchain string. `lexlean lock` records hashes of:

- `lean-toolchain`;
- the one Lake configuration, either `lakefile.toml` or `lakefile.lean`;
- `lake-manifest.json`, when present.

If both Lake configuration forms exist, locking fails. Verification requires the recorded files to match and requires all manifest dependencies to be locally available.

---

## 11. Lock file

### 11.1 General

`lexlean.lock` is generated, canonical TOML with no comments and final LF. Users MUST NOT hand-edit it. `lexlean lock --check` regenerates it in memory and compares exact bytes.

The top-level schema is:

```toml
spec = "lexlean/lock/1"
language = "1.0"
compiler_semantics = "64-lowercase-hex-digits"
project_config_sha256 = "64-lowercase-hex-digits"
lean_toolchain = "leanprover/lean4:v4.32.1"

[[workspace_file]]
path = "lean-toolchain"
sha256 = "..."

[[package]]
id = "lexlean.core"
version = "1.0.0"
kind = "builtin"
source = "embedded"
revision = "compiler-semantics"
tree_sha256 = "..."
manifest_sha256 = "..."
imports = []

[[package]]
id = "example.algebra"
version = "1.2.3"
kind = "path"
source = "glossary/example.algebra"
revision = "none"
tree_sha256 = "..."
manifest_sha256 = "..."
imports = ["lexlean.core@1.0.0"]
```

An optional `[pdf]` lock record mirrors the configured provider and records the hashes of every declared resource.

### 11.2 Canonical ordering

- `workspace_file` rows sort by `path`.
- `package` rows sort by `(id, version)`.
- package `imports` sort lexicographically and contain no duplicates.
- all keys use the order shown by the schema formatter.
- lowercase hexadecimal is mandatory.

### 11.3 Package closure

Every package imported by a source module, and every transitive lexicon import, appears exactly once in the lock. The lock includes `lexlean.core@1.0.0` even though it is automatically loaded.

A source import names an exact package and exact version. Version ranges are not part of language 1.0.

### 11.4 Offline behavior

- `lexlean lock` resolves local and already-cached sources without networking.
- `lexlean lock --allow-network` may acquire missing exact Git commits.
- no other command accepts `--allow-network`;
- verification fails if a locked package is absent or its digest differs;
- an acquired Git package is stored at `<build_root>/cache/git/<revision>/<tree_sha256>/` and is revalidated before use;
- Git submodules, Git LFS indirection, and nested repositories are rejected.

### 11.5 Tree digest

A package tree digest is SHA-256 over:

```text
"lexlean-tree-v1\0"
+ for each regular file in bytewise-sorted project-relative path order:
    u32be(path_byte_length)
    + path_utf8_bytes
    + u64be(file_byte_length)
    + file_bytes
```

Only `lexicon.toml` and files under `entries/` participate. Symlinks, device files, FIFOs, sockets, and non-UTF-8 paths are rejected.

---

## 12. Source normalization and primitive atoms

### 12.1 File encoding

Every `.lex.tex` file MUST be valid UTF-8.

Compilation normalizes CRLF and lone CR to LF, then requires Unicode NFC. A non-NFC file is rejected by `check` with a fix-it; `fmt` rewrites it canonically.

A source file MUST end in one LF and MUST NOT contain:

- NUL;
- tab;
- trailing spaces;
- Unicode line or paragraph separators;
- non-ASCII whitespace;
- a raw percent character;
- a TeX comment;
- a byte-order mark.

A percent sign may appear only through a glossary-defined control sequence such as `\percent`.

### 12.2 Primitive scanner

The primitive scanner recognizes only these atom classes:

1. **control**: backslash followed by one or more ASCII letters, or backslash followed by one ASCII nonletter;
2. **ASCII word**: one or more ASCII letters;
3. **metadata/math identifier**: an ASCII letter followed by zero or more ASCII letters, digits, `_`, or `'`, when the structural or math grammar requests an identifier;
4. **numeral**: one or more ASCII digits;
5. **delimiter**: `{`, `}`, `(`, `)`, `[`, `]`;
6. **ASCII symbol**: one printable ASCII scalar not classified above;
7. **Unicode symbol**: one non-ASCII Unicode scalar;
8. **whitespace**: one or more U+0020 or LF scalars.

The scanner assigns byte and line/column spans. It does not assign mathematical meaning.

The scanner has no dependency on host Unicode character classes. Non-ASCII prose is possible only when its exact scalar sequence is declared as a glossary form.

### 12.3 Core syntax also belongs to the glossary

The compiler embeds the exact bytes and digest of `lexlean.core@1.0.0` and loads it before structural parsing. The lock must identify the same digest. The embedded package is not an implicit prose exception; it is the bootstrap glossary.

Braces, environment delimiters, punctuation, math delimiters, structural controls, and grammar words are entries in `lexlean.core@1.0.0`. They are not accepted merely because TeX recognizes them.

The scanner is the only bootstrapping layer. Every accepted primitive atom after scanning is accounted for by lexical coverage.

### 12.4 No TeX expansion

LexLean does not execute TeX's mouth, macro expander, conditionals, catcodes, package loader, or file inclusion. The following controls are always forbidden in source, whether or not a glossary attempts to declare them:

```text
\def
\gdef
\edef
\xdef
\let
\futurelet
\newcommand
\renewcommand
\providecommand
\input
\include
\usepackage
\documentclass
\csname
\catcode
\write
\read
\openin
\openout
\special
\immediate
\verbatim
\verb
```

The canonical LaTeX backend may emit trusted controls from the renderer-token registry; this does not make those controls legal source escape hatches.

---

## 13. Lexicon packages

### 13.1 Package layout

A lexicon package is:

```text
<package-root>/
├── lexicon.toml
└── entries/
    └── <local-entry-id path>.toml
```

`lexicon.toml` is:

```toml
spec = "lexlean/lexicon/1"
package = "example.algebra"
version = "1.2.3"
language = "1.0"
imports = ["lexlean.core@1.0.0"]
```

Unknown fields and comments are errors. `imports` are exact, sorted, and unique.

A local entry ID is dot-separated lower-case ASCII:

```text
[a-z][a-z0-9-]*(\.[a-z][a-z0-9-]*)*
```

The entry file path is `entries/` plus each dot-separated segment as a directory and `.toml` on the final segment. For example, `nat.add.zero` is stored at `entries/nat/add/zero.toml`.

The globally qualified ID is:

```text
<package-id>::<local-entry-id>
```

### 13.2 Entry schema

Every entry file has:

```toml
spec = "lexlean/entry/1"
id = "nat.add"
category = "infix-function"
signature = "(pi ((explicit a (const lexlean.std.nat::nat)) (explicit b (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))"
surface_arity = 2
frame = "infix"
precedence = 65
associativity = "left"

[denotation]
kind = "lean"
module = "Init.Prelude"
name = "HAdd.hAdd"

[[form]]
id = "plus"
channel = "math"
surface = "+"
canonical_source = true
features = []

[render]
math = "(seq (slot 0) (space) (token plus) (space) (slot 1))"
```

Fields that do not apply to the selected category or denotation are forbidden rather than ignored.

### 13.3 Categories

The exact language-1.0 categories are:

| Category | Semantic role |
|---|---|
| `structural` | Core-only source structure. |
| `grammar` | Core-only determiner, connective, copula, or proof keyword. |
| `label-word` | A concept token allowed in titles and headings. |
| `type-noun` | A type-valued atom or phrase. |
| `term-constant` | A term-valued atom. |
| `function` | A function referenced by explicit call syntax. |
| `prefix-function` | One explicit surface argument. |
| `postfix-function` | One explicit surface argument. |
| `infix-function` | Two explicit surface arguments. |
| `noun-function` | Canonical “the SELF of ARG” function phrase. |
| `binary-noun-function` | Canonical “the SELF of ARG and ARG” phrase. |
| `predicate-constant` | A proposition-valued atom. |
| `adjective-predicate` | Canonical “ARG is SELF” predicate. |
| `intransitive-predicate` | Canonical “ARG SELF” predicate. |
| `transitive-predicate` | Canonical “ARG SELF ARG” predicate. |
| `infix-predicate` | Two-argument mathematical relation. |
| `proof-constant` | A proof term or theorem reference. |

A non-core entry cannot use `structural` or `grammar`.

Category/frame compatibility is exact:

| Category | Permitted frame |
|---|---|
| `structural`, `grammar`, `label-word`, `type-noun`, `term-constant`, `predicate-constant` | `atom` |
| `function` | `call` |
| `prefix-function` | `prefix` |
| `postfix-function` | `postfix` |
| `infix-function`, `infix-predicate` | `infix` |
| `noun-function` | `noun-of` |
| `binary-noun-function` | `binary-noun-of` |
| `adjective-predicate` | `adjective` |
| `intransitive-predicate` | `intransitive` |
| `transitive-predicate` | `transitive` |
| `proof-constant` | `atom` when `surface_arity = 0`, otherwise `call` |

### 13.4 Frames

The exact frame values and surface slot order are:

| Frame | Surface pattern |
|---|---|
| `atom` | `SELF` |
| `call` | `SELF ( ARG_0, ..., ARG_n )` |
| `prefix` | `SELF ARG_0` |
| `postfix` | `ARG_0 SELF` |
| `infix` | `ARG_0 SELF ARG_1` |
| `noun-of` | `the SELF of ARG_0` |
| `binary-noun-of` | `the SELF of ARG_0 and ARG_1` |
| `adjective` | `ARG_0 is SELF` |
| `intransitive` | `ARG_0 SELF` |
| `transitive` | `ARG_0 SELF ARG_1` |

Category/frame compatibility is fixed by the category names above. A package cannot introduce arbitrary grammar productions.

### 13.5 Forms

Each form declares:

- `id`: unique local form ID;
- `channel`: `text`, `math`, or `both`;
- `surface`: exact normalized source spelling;
- `canonical_source`: Boolean;
- `features`: sorted unique values from:
  - `singular`;
  - `plural`;
  - `sentence-case`;
  - `lower-case`;
  - `article-a`;
  - `article-an`.

Rules:

1. leading, trailing, or repeated whitespace in `surface` is forbidden;
2. a surface is parsed into primitive atoms at package-load time;
3. control-sequence forms are aliases only and cannot be canonical source forms for non-core entries;
4. a non-core canonical text form contains only ASCII words and renderer-safe punctuation;
5. a non-core canonical math form contains only renderer-safe ASCII or Unicode symbols;
6. if no safe canonical surface exists, `fmt` emits `\lexeme{qualified-id}`;
7. exactly one canonical source form exists for each channel required by the category;
8. forms are case-sensitive; capitalization variants are separate forms;
9. inflections are explicit; LexLean does not infer plurals or articles;
10. two entries may share a surface, but acceptance then requires unique grammar/type resolution.

### 13.6 Denotations

A denotation is exactly one of:

#### Core

```toml
[denotation]
kind = "core"
constructor = "logic.forall"
```

Only `lexlean.core` may use it.

#### External Lean

```toml
[denotation]
kind = "lean"
module = "Init.Data.Nat.Basic"
name = "Nat.add_zero"
```

The module and name must use the conservative ASCII Lean-name grammar. The entry signature is the complete LexLean interface.

#### Document declaration

```toml
[denotation]
kind = "document"
module = "Main"
component = "double"
```

The declaration must exist in the named LexLean module and match the entry signature.

#### Defined lexicon value

```toml
[denotation]
kind = "defined"
value = "(lam ((explicit n (const lexlean.std.nat::nat))) (app (const lexlean.std.nat::succ) (local n)))"
```

Defined values are nonrecursive, acyclic, and may reference only earlier entries in the package dependency order.

No denotation contains an English description field. Fields named `description`, `documentation`, `note`, `meaning`, or any unknown name are rejected.

### 13.7 Signature requirement

Every semantic entry has a complete signature in the LexLean Semantic Expression encoding in §13.8. The compiler hashes the canonical signature and records the hash in the linked glossary closure.

The signature is an interface declaration checked twice:

1. LexLean uses it for controlled resolution and conservative elaboration.
2. Verification generates an external-interface probe whose Lean elaboration must succeed.

LexLean's Rust checker does not claim to replace Lean's dependent type checker.

### 13.8 LexLean Semantic Expressions (LSE)

LSE is an S-expression language. Its grammar is:

```ebnf
expr        = sort | const | local | app | pi | lam | let | nat ;
sort        = "(" "sort" "prop" ")"
            | "(" "sort" "(" "type" universe ")" ")" ;
const       = "(" "const" qualified-id [universe-args] ")" ;
local       = "(" "local" local-id ")" ;
app         = "(" "app" expr expr {expr} ")" ;
pi          = "(" "pi" "(" binder {binder} ")" expr ")" ;
lam         = "(" "lam" "(" binder {binder} ")" expr ")" ;
let         = "(" "let" local-id expr expr expr ")" ;
nat         = "(" "nat" decimal ")" ;
binder      = "(" binder-mode local-id expr ")" ;
binder-mode = "explicit" | "implicit" | "instance" ;
universe-args = "(" universe {universe} ")" ;
universe    = decimal
            | universe-id
            | "(" "succ" universe ")"
            | "(" "max" universe universe {universe} ")"
            | "(" "imax" universe universe ")" ;
```

Whitespace is one or more ASCII spaces or LF. Comments and quoted strings do not exist.

Rules:

- identifiers are ASCII and validated;
- each local resolves by lexical scope;
- binders are capture-free internal IDs after parsing;
- `app` has at least a function and one argument;
- `pi` and `lam` have at least one binder;
- universe variables are declared by the entry's optional sorted `universes` array;
- all semantic conveniences such as equality, conjunction, existence, and implication are applications of core constants after desugaring;
- canonical LSE prints one ASCII space between atoms, no redundant grouping, and final LF only when stored as a file field;
- alpha-equivalent LSE values are canonicalized by binder order before hashing.

### 13.9 Rendering expressions (LRE)

LRE is the only way a glossary entry influences canonical visible output.

```ebnf
render      = form | self-form | slot | seq | space | token
            | group | paren | bracket | sub | sup | frac
            | operator-name ;
form        = "(" "form" qualified-id form-id ")" ;
self-form   = "(" "self-form" form-id ")" ;
slot        = "(" "slot" decimal ")" ;
seq         = "(" "seq" render {render} ")" ;
space       = "(" "space" ")" ;
token       = "(" "token" renderer-token-id ")" ;
group       = "(" "group" render ")" ;
paren       = "(" "paren" render ")" ;
bracket     = "(" "bracket" render ")" ;
sub         = "(" "sub" render render ")" ;
sup         = "(" "sup" render render ")" ;
frac        = "(" "frac" render render ")" ;
operator-name = "(" "operator-name" ascii-identifier ")" ;
```

Rules:

- raw TeX strings do not exist;
- every `form` references an existing form;
- every `token` references `language/renderer-tokens.toml`;
- every slot index is less than `surface_arity`;
- every explicit surface argument appears exactly once in the canonical render template;
- implicit semantic parameters are not surface slots;
- `operator-name` accepts only `[A-Za-z][A-Za-z0-9_]*`;
- non-core packages cannot define renderer tokens;
- renderer expressions are acyclic.

### 13.10 Renderer-token registry

`language/renderer-tokens.toml` is the single source for trusted LaTeX controls and mathematical glyphs. Each row declares:

- token ID;
- exact emitted UTF-8 bytes;
- channel;
- arity;
- whether grouping is required;
- source package authority, always core.

The language-1.0 registry MUST be the minimal transitive closure of tokens referenced by the exact preamble, core LRE, and shipped standard-package LRE. Unused rows fail the language audit. It MUST contain the following semantic token IDs; document/package options and environment names in the fixed preamble are also individual core rows rather than unclassified text:

```text
documentclass
usepackage
newtheorem
theoremstyle
begin
end
center
large
section
subsection
label
texttt
operatorname
mathbb
mathrm
proof
definition
theorem
lemma
corollary
plus
minus
times
cdot
slash
equals
not-equals
less
less-equal
greater
greater-equal
member
not-member
subset
subset-equal
union
intersection
forall
exists
exists-unique
logical-and
logical-or
logical-not
implies
iff
mapsto
arrow
left-arrow
comma
period
colon
semicolon
left-paren
right-paren
left-bracket
right-bracket
```

Canonical math bytes are fixed: logical conjunction is `\land`, disjunction `\lor`, negation `\lnot`, implication `\to`, equivalence `\leftrightarrow`, universal quantification `\forall`, existence `\exists`, unique existence `\exists!`, membership `\in`, and set inclusion `\subseteq` where the corresponding token is used. Preamble option/package/environment atoms, braces, separators, and dynamically generated validated labels are all covered by core structural rows or source-derived metadata rows.

A renderer token is not a source macro facility. It is a closed compiler datum included in the compiler-semantics hash.

### 13.11 Package validation

Loading a package MUST reject:

- schema mismatch;
- package/version mismatch with the lock;
- unknown fields;
- comments;
- duplicate package or entry IDs;
- invalid entry paths;
- invalid forms;
- missing canonical forms;
- form/category incompatibility;
- invalid LSE or LRE;
- unresolved references;
- import cycles;
- defined-denotation cycles;
- invalid renderer slots;
- raw control output;
- a document denotation whose declaration is unavailable;
- an eliminator descriptor that references absent constructors.

---

## 14. Lexical resolution

### 14.1 Token lattice

LexLean builds a token lattice rather than committing greedily to one segmentation.

For each source position, it records every glossary form whose primitive-atom sequence begins there. Whitespace between atoms in a multiword form is equivalent to one separator. The parser may select any path that:

- begins at the component's first non-whitespace atom;
- ends at its last non-whitespace atom;
- covers every non-whitespace atom exactly once;
- respects structural channel boundaries;
- stays below `max_token_lattice_edges`.

Import order gives no priority.

### 14.2 Scoped identifiers

A local identifier is accepted before global glossary resolution only in an explicit binder position. The binder creates a scoped lexical declaration. Every later occurrence must resolve to that declaration or a different explicit global selection.

Local scope order is:

1. inherited section parameters;
2. declaration binders;
3. proof locals and hypotheses;
4. branch binders.

Inner locals shadow an identically spelled outer local. Local identifiers do not shadow text glossary forms.

### 14.3 Explicit qualification

`\lexeme{package::entry}` selects one glossary entry. The control and every delimiter are core entries; the qualified ID is structural metadata.

`\reference{Module::component}` selects one document declaration as a proof term. It is valid only when the module is imported or current and the declaration precedes the reference.

Qualified selection is canonicalized back to the entry's safe canonical surface when possible. It never injects arbitrary output.

### 14.4 Ambiguity

The parser and elaborator retain alternatives until:

- grammar-category constraints;
- scope;
- arity;
- expected semantic category;
- declared signatures; and
- conservative type unification

remove them.

Distinct alternatives that canonicalize to the same linked IR are collapsed. If more than one distinct linked IR remains, compilation fails with `LLP2002` and presents the minimal differentiating spans and qualified candidate IDs.

No package order, frequency, capitalization heuristic, or external language model may select a meaning.



## 15. LexLean document grammar

### 15.1 Structural grammar

The structural grammar is fixed. Environment and control names are literal core entries.

```ebnf
module          = "\begin{lexlean}" "{" module-name "}"
                  header
                  block*
                  "\end{lexlean}" ;

header          = use-glossary*
                  import-module*
                  title ;

use-glossary    = "\useglossary" "{" package-id "@" semver "}" ;
import-module   = "\importmodule" "{" module-name "}" ;
title           = "\title" "{" phrase "}" ;

block           = section | declaration ;

section         = "\begin{section}" "{" component-id "}"
                  "\heading" "{" phrase "}"
                  [parameters]
                  block*
                  "\end{section}" ;

parameters      = "\parameters" "{" binder-list "}" ;

declaration     = type-definition
                | term-definition
                | predicate-definition
                | theorem
                | lemma
                | corollary ;

type-definition = "\begin{typedefinition}"
                  "{" component-id "}"
                  "{" qualified-entry-id "}"
                  axiom-policy
                  type-definition-sentence
                  "\end{typedefinition}" ;

term-definition = "\begin{termdefinition}"
                  "{" component-id "}"
                  "{" qualified-entry-id "}"
                  axiom-policy
                  term-definition-sentence
                  "\end{termdefinition}" ;

predicate-definition
                = "\begin{predicatedefinition}"
                  "{" component-id "}"
                  "{" qualified-entry-id "}"
                  axiom-policy
                  predicate-definition-sentence
                  "\end{predicatedefinition}" ;

theorem         = "\begin{theorem}" "{" component-id "}"
                  axiom-policy proposition-sentence proof
                  "\end{theorem}" ;

lemma           = "\begin{lemma}" "{" component-id "}"
                  axiom-policy proposition-sentence proof
                  "\end{lemma}" ;

corollary       = "\begin{corollary}" "{" component-id "}"
                  axiom-policy proposition-sentence proof
                  "\end{corollary}" ;

proof           = "\begin{proof}" proof-step+ "\end{proof}" ;

axiom-policy    = "\noaxioms"
                | "\allowaxioms" "{" lean-name-list "}"
                | "\exactaxioms" "{" lean-name-list "}" ;
```

Rules:

- imports occur only in the header;
- `\useglossary` rows sort by package reference under `fmt`;
- `\importmodule` rows sort by module name under `fmt`;
- each module has exactly one title;
- section nesting is allowed up to `max_scope_depth`;
- section component IDs and declaration component IDs share one module-wide namespace;
- component IDs match `[a-z][a-z0-9-]*`;
- module names are relative to `module_prefix`;
- the full generated Lean module is `<module_prefix>.<module-name>`;
- an imported module must be a project module and must not create an import cycle;
- a selected build includes the transitive import closure;
- a source module may import only declarations exported by an explicitly imported module;
- no declaration may reference a later declaration in the same module;
- an empty module is valid, but a theorem-like declaration without a proof is not.

### 15.2 Core structural controls

The complete structural control set for language 1.0 is:

```text
\begin
\end
\useglossary
\importmodule
\title
\heading
\parameters
\noaxioms
\allowaxioms
\exactaxioms
\lexeme
\reference
\forward
\backward
\rule
\start
\step
\bind
\(
\)
\[
\]
```

The complete environment-name set is:

```text
lexlean
section
typedefinition
termdefinition
predicatedefinition
theorem
lemma
corollary
proof
have
rewrite
simplify
apply
constructor
branch
premise
cases
case
induction
calculate
```

Any other control or environment name is unknown unless it is a nonstructural glossary form accepted in the current expression channel. A glossary cannot add an environment.

### 15.3 Phrases

A `type-phrase` is either one linked `type-noun` frame, including its explicit surface arguments, or one math island whose result is a sort.

A `phrase` is a nonempty sequence of:

- `label-word`;
- `type-noun`;
- the canonical nominal form of a term or function entry;
- a math island containing a term whose result is not `Prop`;
- core punctuation `:`, `-`, `(`, or `)`.

A phrase cannot contain:

- a proposition;
- a quantifier;
- a predicate frame;
- a proof instruction;
- an unbound pronoun;
- an adverbial assertion.

Titles and headings therefore identify concepts but do not make unproved claims.

### 15.4 Binder lists

A text binder has:

```ebnf
binder      = type-phrase math-new-local ;
binder-list = binder { ";" binder } ;
```

Example:

```latex
\parameters{natural number \(n\); natural number \(m\)}
```

A `math-new-local` is a math island containing exactly one fresh ASCII identifier. The identifier is a display spelling; the IR assigns a unique `LocalId`.

All source binders are explicit. Implicit and instance binders may exist in external signatures, but language 1.0 does not let document prose silently introduce them.

### 15.5 Mathematical islands

Only `\(...\)` and `\[...\]` delimit mathematical islands. Dollar delimiters are forbidden.

Inside a math island:

- spaces and LF are insignificant separators;
- parentheses group;
- comma separates explicit call arguments;
- a local identifier resolves through scope;
- a numeral uses the core numeral constructor;
- `\lexeme{qualified-id}` explicitly selects an entry;
- `\reference{Module::component}` selects an earlier or imported document declaration;
- glossary frames supply prefix, postfix, and infix syntax;
- function application is `f(arg_0, ..., arg_n)`;
- juxtaposition is never implicit multiplication or application;
- braces do not group mathematical terms;
- `_` has no built-in subscript meaning;
- every operator has declared precedence and associativity.

The Pratt precedence scale is `0..255`; higher values bind more tightly. An infix operator declares `left`, `right`, or `none`. A nonassociative chain without parentheses is an ambiguity error.

Numerals have no default type. A numeral must receive an expected type from an operator, relation, binder, definition signature, or declaration statement. Otherwise elaboration fails.

### 15.6 Proposition grammar

The controlled proposition grammar is:

```ebnf
proposition-sentence = proposition "." ;

proposition    = conditional ;

conditional    = "if" proposition "," "then" proposition
               | equivalence ;

equivalence    = implication
                 [ "if" "and" "only" "if" implication ] ;

implication    = disjunction
                 [ "implies" implication ] ;

disjunction    = conjunction { "or" conjunction } ;

conjunction    = negation { "and" negation } ;

negation       = "not" negation
               | quantified
               | atomic-proposition ;

quantified     = "For" "every" binder
                 { "and" binder } ","
                 proposition
               | "for" "every" binder
                 { "and" binder } ","
                 proposition
               | "there" "exists" article binder
                 "such" "that" proposition
               | "there" "exists" "exactly" "one" binder
                 "such" "that" proposition ;

article        = "a" | "an" ;

atomic-proposition
              = math-proposition
              | predicate-frame ;
```

The lowercase `for every` form is accepted after a grammar boundary; sentence-initial canonical output uses `For`.

A `math-proposition` is a math island whose linked result is `Prop`.

A `predicate-frame` is one of the fixed predicate frames declared in §13.4. Its semantic denotation is application of that entry to its surface arguments.

Compositional semantics are:

| Surface | IR |
|---|---|
| `For every x, P` | dependent `Pi` into `Prop` |
| `there exists a x such that P` | `Exists (fun x => P)` |
| `there exists exactly one x such that P` | `ExistsUnique (fun x => P)` |
| `if P, then Q` or `P implies Q` | implication |
| `P if and only if Q` | `Iff P Q` |
| `P and Q` | `And P Q` |
| `P or Q` | `Or P Q` |
| `not P` | `Not P` |

Core logical words have no user-overridable denotation.

### 15.7 Definition sentences

A type definition has exactly one of these forms:

```text
A SELF-TYPE is defined as TYPE.
An SELF-TYPE is defined as TYPE.
For every BINDER-LIST, a SELF-TYPE is defined as TYPE.
For every BINDER-LIST, an SELF-TYPE is defined as TYPE.
```

A term definition has exactly one of:

```text
SELF-TERM is defined as TERM.
For every BINDER-LIST, SELF-APPLICATION is defined as TERM.
```

A predicate definition has exactly one of:

```text
SELF-PREDICATE holds exactly when PROPOSITION.
For every BINDER-LIST, SELF-PREDICATE holds exactly when PROPOSITION.
```

Validation requirements:

1. `SELF` is the entry named in the declaration header.
2. Its denotation is `document` and names the current module and component.
3. Its signature agrees with the declaration kind.
4. Each explicit signature binder occurs exactly once in the self application and in signature order.
5. The right-hand side has the declared result category.
6. The right-hand side does not reference the declaration being defined.
7. The declaration references no later local declaration.
8. The definition graph is acyclic.
9. A type definition emits a nonrecursive Lean `def` whose result is a sort.
10. A predicate definition emits a nonrecursive Lean `def` returning `Prop`.
11. No definitional component accepts a proof environment.

### 15.8 Theorem-like components

A theorem, lemma, or corollary contains:

1. exactly one axiom policy;
2. exactly one proposition sentence;
3. exactly one proof;
4. no other text.

Quantified locals in the proposition are in scope throughout the proof. The declaration's Lean type is generated from the proposition IR, not from a separate signature field.

The three kinds all emit Lean `theorem`; their distinction affects canonical document labeling and IR metadata.

### 15.9 Axiom-policy syntax

`\noaxioms` means the observed set must be empty.

`\allowaxioms{A;B;C}` means the observed set must be a subset of the listed set.

`\exactaxioms{A;B;C}` means the observed set must equal the listed set.

A Lean-name list:

- uses semicolon separators;
- contains fully qualified conservative ASCII Lean names;
- is nonempty for `allow` and `exact`;
- contains no duplicates;
- is sorted by `fmt`;
- is recorded exactly in IR and manifests.

Every definition and theorem-like declaration requires a policy. There is no inherited module policy and no implicit default.

---

## 16. Structured proof language

### 16.1 General semantics

A proof is a structured program over one current goal and an ordered local context. It is not English passed to an interpreter and not Lean tactic text.

Each simple proof sentence or structured proof environment constructs one `Proof` IR node. The Lean backend lowers that node to a fixed tactic pattern.

A proof block MUST leave no goals. LexLean performs conservative structural checking; Lean elaboration is final. A proof that Rust accepts but Lean rejects is a verification failure, never a verified result.

### 16.2 Simple proof sentences

The exact simple sentences are:

```text
Assume \(x\).
Assume \(x\), \(y\).
Apply TERM.
Close the goal with TERM.
Close the goal by reflexivity.
Use TERM as the witness.
Select the left alternative.
Select the right alternative.
```

Semantics:

| Sentence | IR / Lean lowering |
|---|---|
| `Assume ...` | introduce the next leading goal binders; lower to `intro` |
| `Apply TERM.` | apply a proof term; valid only when exactly one residual goal remains |
| `Close the goal with TERM.` | `exact TERM` |
| `Close the goal by reflexivity.` | `rfl` |
| `Use TERM as the witness.` | provide the next existential witness |
| `Select the left alternative.` | choose `Or.inl` |
| `Select the right alternative.` | choose `Or.inr` |

A local named by `Assume` must be fresh in the current proof scope. The displayed spelling is mapped to a deterministic generated Lean local name.

### 16.3 Have

Syntax:

```latex
\begin{have}{h}
PROPOSITION.
\begin{proof}
PROOF-STEPS
\end{proof}
\end{have}
```

The nested proof establishes the proposition and introduces `h` for all subsequent steps in the containing proof block. Lowering is:

```lean
have <generated-h> : <proposition> := by
  <nested-proof>
```

The nested proof cannot see `h` before it is established.

### 16.4 Rewrite

Syntax:

```latex
\begin{rewrite}{goal}
\forward{PROOF-TERM}
\backward{PROOF-TERM}
\forward{PROOF-TERM}
\end{rewrite}
```

or with a hypothesis target:

```latex
\begin{rewrite}{h}
...
\end{rewrite}
```

Rules:

- the target is exactly `goal` or an in-scope proof-local spelling;
- at least one rule is required;
- rules are applied strictly in source order;
- `\forward` uses the equality or equivalence left-to-right;
- `\backward` uses it right-to-left;
- each rule contains exactly one proof term;
- no global rewrite set is consulted.

Lean lowering is a single `rw` command with ordered rules and explicit reverse markers, optionally `at <target>`.

This ordered, per-rule direction model is the complete multi-rule rewrite semantics.

### 16.5 Simplify

Syntax:

```latex
\begin{simplify}{goal}
\rule{PROOF-TERM}
\rule{PROOF-TERM}
\end{simplify}
```

The target rule is the same as rewrite. At least one rule is required.

Lowering uses `simp only [rules...]`, optionally at one named hypothesis. The ambient simp theorem set is not used. Kernel reduction and the fixed behavior of pinned Lean's `simp only` remain part of the Lean toolchain.

### 16.6 Structured apply

When application yields zero or more than one residual premise, the structured form is required:

```latex
\begin{apply}{PROOF-TERM}
\begin{premise}{1}
PROOF-STEPS
\end{premise}
\begin{premise}{2}
PROOF-STEPS
\end{premise}
\end{apply}
```

Rules:

- premise labels are consecutive decimal integers beginning with 1;
- every residual premise occurs exactly once;
- each premise is a nested proof scope;
- branch order follows the explicit premise order in the selected proof constant's declared signature;
- a mismatch is a proof-shape diagnostic before Lean invocation when the signature suffices, otherwise a remapped Lean diagnostic.

### 16.7 Constructor

Syntax:

```latex
\begin{constructor}
\begin{branch}{1}
PROOF-STEPS
\end{branch}
\begin{branch}{2}
PROOF-STEPS
\end{branch}
\end{constructor}
```

The branch count and order must match the target constructor's explicit proof fields. This form covers conjunction, biconditional constructors, and explicitly declared structures available through glossary metadata.

### 16.8 Cases

Syntax:

```latex
\begin{cases}{TERM}
\begin{case}{qualified-constructor-entry}
\bind{x;y}
PROOF-STEPS
\end{case}
\end{cases}
```

Requirements:

- the scrutinee type has a glossary eliminator descriptor;
- every constructor appears exactly once;
- case order is canonicalized to descriptor order;
- `\bind{}` contains a semicolon-separated list of fresh local spellings;
- binder count matches the descriptor's constructor fields;
- branch locals are scoped to the case;
- the backend emits pinned Lean `cases` syntax with named alternatives.

### 16.9 Induction

Syntax:

```latex
\begin{induction}{TERM}
\begin{case}{qualified-constructor-entry}
\bind{x;ih}
PROOF-STEPS
\end{case}
\end{induction}
```

Requirements mirror cases. The eliminator descriptor distinguishes constructor fields from induction hypotheses and fixes their binding order. Every case occurs exactly once.

The backend emits pinned Lean `induction` syntax. LexLean does not synthesize an induction principle or infer missing cases.

### 16.10 Calculation chains

Syntax:

```latex
\begin{calculate}
\start{TERM}
\step{qualified-relation-entry}{TERM}{PROOF-TERM}
\step{qualified-relation-entry}{TERM}{PROOF-TERM}
\end{calculate}
```

Rules:

- at least one step is required;
- every relation entry is identical;
- the relation has a glossary calculation descriptor;
- each proof term establishes the relation from the previous term to the new term;
- the first and last terms match the current goal's endpoints;
- language 1.0 ships an equality calculation descriptor;
- mixed-relation transitivity is not accepted.

The Lean backend emits a `calc` block.

### 16.11 Eliminator descriptors

A type entry may contain:

```toml
[eliminator]
cases_lean_name = "Nat.casesAuxOn"
induction_lean_name = "Nat.recAux"

[[eliminator.constructor]]
entry = "lexlean.std.nat::zero"
lean_name = "Nat.zero"
fields = []
induction_hypotheses = []

[[eliminator.constructor]]
entry = "lexlean.std.nat::succ"
lean_name = "Nat.succ"
fields = ["n"]
induction_hypotheses = ["ih"]
```

The descriptor is an interface, not trusted proof. External-interface probes and actual generated proofs must elaborate under Lean.

### 16.12 Forbidden proof forms

The proof parser MUST reject:

- arbitrary imperative sentences;
- unregistered synonyms;
- raw tactic blocks;
- tactic quotations;
- semicolon tactic combinators;
- tactic repetition;
- unrestricted simplification;
- unrestricted search;
- `native_decide`;
- generated or authored proof holes;
- an empty proof;
- a proof step after the current branch has closed;
- a branch that does not close.

---

## 17. Semantic elaboration and IR

### 17.1 Compiler phases

The required phase order is:

1. locate project root;
2. parse and validate project configuration;
3. read and validate lock;
4. normalize and scan source;
5. load and validate lexicon closure;
6. build primitive-atom coverage and token lattice;
7. parse structural components;
8. parse terms, propositions, and proofs;
9. resolve globals and locals;
10. conservatively elaborate candidates;
11. reject zero or multiple distinct interpretations;
12. link modules and document declarations;
13. construct linked IR;
14. validate every declaration and proof shape;
15. compute source and semantic content IDs;
16. render artifacts;
17. optionally verify.

No backend is invoked before linked IR is complete.

### 17.2 Core reference types

A global reference is exactly:

```rust
pub enum GlobalRef {
    Core(CoreRef),
    External(ExternalConstRef),
    Document(DocumentDeclRef),
    DefinedLexicon(DefinedLexiconRef),
}
```

`ExternalConstRef` contains:

```rust
pub struct ExternalConstRef {
    pub package: QualifiedPackageId,
    pub entry: QualifiedEntryId,
    pub lean_module: LeanModuleName,
    pub lean_name: LeanName,
    pub signature_hash: Sha256Digest,
}
```

A document reference contains logical module and component IDs plus the linked generated Lean name.

A local reference is `LocalId`, an opaque monotonically assigned integer unique within one linked project. Display spellings are metadata, not identity.

### 17.3 Term IR

The linked term IR MUST be capable of representing:

```rust
pub enum Term {
    Sort(Universe),
    Local(LocalId),
    Global(GlobalRef, Vec<Universe>),
    App {
        function: Box<Term>,
        explicit_args: Vec<Term>,
        omitted_implicit_binders: Vec<ImplicitBinderId>,
    },
    Pi {
        binders: Vec<Binder>,
        body: Box<Term>,
    },
    Lambda {
        binders: Vec<Binder>,
        body: Box<Term>,
    },
    Let {
        binder: Binder,
        value: Box<Term>,
        body: Box<Term>,
    },
    NatLiteral {
        decimal: String,
        expected_type: Box<Term>,
    },
}
```

Logical surface constructs are desugared to applications of core globals. There is no opaque prose term.

### 17.4 Proof IR

The proof IR contains exactly:

```rust
pub enum Proof {
    Sequence(Vec<ProofStep>),
    Intro(Vec<LocalId>),
    Exact(Term),
    ApplyOne(Term),
    Apply {
        function: Term,
        premises: Vec<Proof>,
    },
    Reflexivity,
    Witness(Term),
    SelectLeft,
    SelectRight,
    Have {
        local: LocalId,
        proposition: Term,
        proof: Box<Proof>,
    },
    Rewrite {
        target: RewriteTarget,
        rules: Vec<RewriteRule>,
    },
    SimplifyOnly {
        target: RewriteTarget,
        rules: Vec<Term>,
    },
    Constructor(Vec<Proof>),
    Cases {
        scrutinee: Term,
        cases: Vec<CaseProof>,
    },
    Induction {
        scrutinee: Term,
        cases: Vec<CaseProof>,
    },
    Calculate {
        relation: GlobalRef,
        start: Term,
        steps: Vec<CalculationStep>,
    },
}
```

No “custom”, “raw”, “plugin”, or “unknown” variant exists.

### 17.5 Document IR

A linked project contains a sorted map of `ModuleName` to `DocumentModule`. A module contains:

- normalized source identity;
- explicit glossary closure;
- explicit module imports;
- title phrase IR;
- ordered sections;
- ordered declarations;
- complete origin tables.

A declaration contains:

- source component ID;
- generated Lean name;
- declaration kind;
- inherited section parameters;
- statement or definition term;
- optional proof, required exactly when theorem-like;
- explicit axiom policy;
- origin node ID.

### 17.6 Conservative type-directed resolution

LexLean uses glossary signatures to:

- check arity;
- instantiate explicit binders;
- propagate expected categories and types;
- resolve overloaded lexical candidates;
- reject syntactically impossible applications;
- record omitted implicit binders.

LexLean MUST NOT claim complete Lean definitional equality. If conservative elaboration cannot choose uniquely, it rejects rather than delegating candidate choice to Lean. Lean may still reject a unique LexLean IR, and such rejection is a verification failure.

### 17.7 Definition linking

Document-entry signatures are compared against declaration statements using canonical LSE after local-binder substitution. A mismatch is detected before rendering.

Document declarations are available only after their source position. Module imports expose all exported declarations of the imported module.

### 17.8 Name generation

- Full module: `<module_prefix>.<source-module>`.
- Component Lean name: component ID with `-` changed to `_`.
- A component ID whose conversion collides with another component or a Lean keyword is rejected.
- Generated local names are `llv0`, `llv1`, ... in binder-introduction order.
- Generated proof hypothesis names are `llh0`, `llh1`, ... .
- Source spellings are retained for canonical LaTeX and diagnostics.
- `set_option autoImplicit false` is always emitted.

### 17.9 Canonical IR serialization

The semantic ID uses a canonical JSON serialization of linked IR:

- schema-tagged;
- no floating-point values;
- object keys in ASCII byte order;
- arrays in semantic order;
- lower-case hexadecimal;
- minimal JSON escaping;
- no insignificant whitespace;
- no trailing LF in the hashed payload.

Opaque Rust debug output is never hashed or exposed as a stable format.



## 18. Lean backend

### 18.1 Output contract

For each LexLean module, the backend emits one `.lean` file under a path matching the full generated module name.

The file structure is exactly:

```lean
module
import <sorted external and generated modules>
set_option autoImplicit false
namespace <full generated module>

<declarations in source order>

end <full generated module>
```

There are no comments or blank documentation blocks. The file ends in one LF.

### 18.2 Prose-free rule

Generated Lean MUST contain no:

- line comment;
- block comment;
- documentation comment;
- string literal;
- character literal used as documentation;
- command whose purpose is textual output, except the separate axiom-audit module;
- source-text copy;
- glossary description;
- `sorry`;
- `admit`;
- `axiom`;
- `opaque`;
- `unsafe`;
- `native_decide`;
- placeholder declaration.

A generated-source audit lexes every `.lean` file before verification. It checks tokens, not substring guesses, so legal identifier fragments are not misclassified.

### 18.3 Names and imports

- all imports are explicit, deduplicated, and bytewise sorted;
- every external global is emitted by fully qualified Lean name;
- generated-module imports use their full generated names;
- no `open`, `open scoped`, namespace alias, or imported notation is emitted;
- imported notation is not relied upon for semantic lowering;
- source order is retained for declarations;
- inherited section parameters are emitted explicitly on each declaration that uses them;
- unused section parameters are not added to a declaration.

### 18.4 Term lowering

The backend favors explicit core applications over presentation notation:

- equality lowers to `Eq`;
- conjunction to `And`;
- disjunction to `Or`;
- negation to `Not`;
- existence to `Exists`;
- unique existence to `ExistsUnique`;
- equivalence to `Iff`;
- external functions use fully qualified constants;
- binders preserve explicit, implicit, and instance modes from linked signatures;
- numerals use Lean numeral syntax with an expected type.

The renderer MAY use parentheses to make every application and binder unambiguous. Output formatting is fixed at two spaces per tactic or branch indentation and never depends on a pretty-printer version.

### 18.5 Leading universal binders

Leading universal binders in a theorem statement are lambda-lifted into Lean declaration parameters in source order. They are already in scope when the proof begins. A proof-level `Assume` therefore introduces only binders remaining in the current goal after declaration parameters.

The IR retains the original proposition, and the source map relates both the parameter and body ranges to the quantified source clause.

### 18.6 Definitions

Type, term, and predicate definitions emit `def`, never `abbrev`, `opaque`, or `theorem`.

A document definition is nonrecursive. Its generated type is explicit. The generated value contains no compiler-invented assumption.

### 18.7 Proof lowering

Proof IR lowers only to these pinned Lean forms:

```text
intro
exact
apply
rfl
refine
constructor
left
right
have
rw
simp only
cases ... with
induction ... with
calc
```

The backend does not accept backend-specific user text. Tactic forms are emitted solely from structured proof IR.

### 18.8 External-interface probe module

Verification generates a probe module named:

```text
LexLeanProbe.P<first-32-hex-of-semantic-id>
```

For every used external Lean entry, sorted by qualified entry ID, it emits an `example` whose declared type is the entry's linked signature and whose value is the external Lean constant. Universe variables are alpha-renamed with an entry-index prefix.

The probe establishes only that the external constant can inhabit the declared interface in the pinned environment. It is not included in the canonical document, module API, or axiom-policy results.

A preexisting module with the reserved probe name is an environment conflict and causes verification to fail. Before any compilation, LexLean also rejects a preexisting workspace/search-path module whose full name equals any generated document module.

### 18.9 Axiom-audit module

Verification generates an audit module named:

```text
LexLeanAudit.A<first-32-hex-of-semantic-id>
```

It imports every generated module in sorted order and emits one:

```lean
#print axioms <fully-qualified-declaration-name>
```

for every generated definition and theorem-like declaration in sorted fully qualified name order.

The audit module contains no other command and no comments. Its source and normalized output are verification artifacts.

A preexisting module with the reserved audit name is an environment conflict and causes verification to fail.

---

## 19. Canonical LaTeX and PDF

### 19.1 Canonical LaTeX is generated, not copied

The LaTeX backend consumes linked IR. It MUST NOT copy an author's sentence, alias spelling, whitespace, TeX control, or punctuation directly into output.

Every visible output word is produced from a canonical glossary form. Every mathematical construct is produced through LRE and the renderer-token registry. Every structural control is produced by the fixed backend. Every non-whitespace canonical-TeX atom, including fixed preamble options, package names, environment names, braces, labels, and separators, receives an output-coverage origin.

### 19.2 Exact preamble

Each module emits a standalone `.tex` file with this logical preamble and order:

```latex
\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage[hidelinks]{hyperref}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\begin{document}
```

The file ends with:

```latex
\end{document}
```

No comment, author, date, timestamp, generator banner, path, or host metadata is emitted.

### 19.3 Document rendering

- The title is rendered in a `center` environment with `\LARGE`.
- Source sections render as `\section{...}` and nested sections as `\subsection{...}`. Nesting beyond two levels continues with a deterministic bold heading construct registered in the renderer.
- Section parameters render immediately below the heading as a display labeled by the core glossary concept `Parameters`.
- Type, term, and predicate definitions render in `definition`.
- Theorem-like kinds use their corresponding environments.
- Every component receives:
  ```latex
  \label{ll:<module-slug>:<component-id>}
  ```
- Statements render from proposition or definition IR.
- Proofs render from proof IR using the canonical proof phrases in `lexlean.core`.
- Imported-module lists are not human-visible claims and are omitted.
- The file uses LF and one final LF.

### 19.4 Canonical proposition rendering

Canonical prose uses the controlled grammar:

- leading `For every`;
- `there exists`;
- `there exists exactly one`;
- `if ..., then ...`;
- `if and only if`;
- `and`, `or`, and `not`;
- canonical predicate frames.

Parentheses are inserted when grammar precedence would otherwise change the IR. Mathematical terms use canonical LRE.

### 19.5 Canonical proof rendering

Proof IR renders to fixed formal prose. Representative mappings are:

| Proof IR | Canonical text |
|---|---|
| `Intro` | `Assume ... .` |
| `Exact` | `The goal follows from ... .` |
| `ApplyOne` | `Apply ... .` |
| `Reflexivity` | `The goal follows by reflexivity.` |
| `Have` | `We first establish ... .` followed by its nested proof |
| `Rewrite` | `Rewrite ... using ... .` with every direction stated |
| `SimplifyOnly` | `Simplify ... using only ... .` |
| `Cases` | `Consider the cases of ... .` |
| `Induction` | `Proceed by induction on ... .` |
| `Calculate` | a displayed aligned chain |

These words are core glossary entries. The renderer never invents synonyms.

### 19.6 Output lexical coverage

For every canonical `.tex`, LexLean emits a coverage record proving mechanically that:

- every visible word maps to a glossary entry;
- every mathematical token maps to a glossary entry, local, numeral, or core constructor;
- every control sequence maps to a renderer token;
- every punctuation mark maps to core grammar or renderer data;
- no raw output segment is unclassified.

Failure to produce complete output coverage is a backend error and prevents artifact publication.

### 19.7 External PDF provider

PDF output is optional and has no proof authority.

When configured, `lexlean verify`:

1. verifies the provider executable SHA-256;
2. invokes `version_argv` with no shell;
3. normalizes stdout and verifies `version_stdout_sha256`;
4. creates an isolated temporary working directory;
5. copies only the canonical `.tex` and declared regular resource files into it;
6. expands only the whole-argument placeholders:
   - `{input}`;
   - `{out_dir}`;
   - `{stem}`;
7. invokes `compile_argv` directly, with no shell parsing;
8. enforces child timeout and output-size limits;
9. requires exactly the configured output regular file;
10. requires the bytes to begin with `%PDF-`;
11. copies the PDF atomically into the platform-bound verification artifact set;
12. records process, recipe, and output hashes.

PDF bytes and process records are not placed in the platform-independent build directory.

A placeholder embedded in a larger argument is forbidden. Each required placeholder must occur exactly once where the schema requires it. The provider receives no project directory as its working directory and no undeclared resource.

### 19.8 PDF recipe content address

The PDF recipe ID is:

```text
SHA256(
  "lexlean-pdf-recipe-v1\0"
  || frame("tex", canonical_tex_sha256_bytes)
  || frame("program", program_sha256_bytes)
  || frame("version-output", version_stdout_sha256_bytes)
  || frame("argv", canonical_json(compile_argv))
  || frame("resources", canonical_json(sorted resource path/hash rows))
)
```

The actual PDF SHA-256 is recorded separately. The recipe and PDF are platform-bound evidence and do not affect `semantic_id`.

---

## 20. Diagnostics, source maps, and coverage

### 20.1 Diagnostic object

Every diagnostic serializes as:

```json
{
  "spec": "lexlean/diagnostic/1",
  "code": "LLL1004",
  "severity": "error",
  "message": "unknown source atom",
  "primary": {
    "path": "src/Main.lex.tex",
    "byte_start": 120,
    "byte_end": 129,
    "line_start": 7,
    "column_start": 5,
    "line_end": 7,
    "column_end": 14
  },
  "labels": [],
  "notes": [],
  "help": [],
  "causes": []
}
```

Offsets are zero-based half-open UTF-8 byte offsets. Lines and columns are one-based; columns count Unicode scalar values after normalization.

Object keys are canonicalized. Diagnostics sort by:

1. project-relative path;
2. byte start;
3. severity;
4. code;
5. message.

### 20.2 Severity

Language 1.0 compiler diagnostics are either `error` or attached `note`/`help`. There is no recoverable compiler warning category.

Any warning emitted by Lean, Lake, `leanchecker`, or a PDF provider is a verification failure unless the output is the expected informational result of the generated axiom-audit commands.

### 20.3 Source-map schema

Each module map contains:

```json
{
  "spec": "lexlean/source-map/1",
  "source_id": "...",
  "semantic_id": "...",
  "module": "Main",
  "sources": [],
  "artifacts": [],
  "nodes": [],
  "mappings": []
}
```

A mapping identifies:

- artifact kind and relative path;
- generated half-open byte range;
- source file and half-open byte range, or a synthetic core/glossary origin;
- IR node ID;
- role: `declaration`, `binder`, `term`, `proof`, `structure`, `renderer`, or `synthetic`.

Every non-whitespace generated Lean token and every canonical LaTeX token/control has at least one mapping. Boilerplate maps to explicit synthetic origins such as `core:lean-preamble/1`, never to a fabricated source span.

### 20.4 Lean diagnostic remapping

Verification parses Lean locations against generated files. It selects the smallest generated mapping that encloses the reported byte position. Ties are resolved by:

1. shortest generated range;
2. non-synthetic before synthetic;
3. lowest stable IR node ID.

The remapped diagnostic contains both:

- the primary LexLean source span;
- the generated Lean location as a note.

If an external Lean diagnostic has no generated mapping, the primary location is the declaration component and the unmapped generated path/range is retained as a note.

### 20.5 Coverage schema

Each module coverage file contains sorted rows for:

- source primitive atoms;
- selected lexical forms;
- scoped declarations;
- canonical LaTeX visible tokens;
- canonical LaTeX controls;
- generated Lean semantic tokens.

Every source atom row records exactly one selected binding. Whitespace rows are optional; non-whitespace rows are mandatory. Overlap or a gap is an internal invariant failure.

### 20.6 Diagnostic output modes

The CLI supports:

- `human`: deterministic text to stderr, optional color;
- `json`: one canonical JSON command-result object to stdout and no human diagnostic text.

JSON output has no timestamps, absolute paths, or terminal escape sequences.

The one command-result object is:

```json
{
  "spec": "lexlean/command-result/1",
  "command": "check",
  "success": false,
  "exit_code": 1,
  "modules": [],
  "artifacts": [],
  "diagnostics": []
}
```

Absent IDs are omitted rather than encoded as JSON `null`. Module and artifact rows are sorted. `success` is true exactly when `exit_code` is zero.

---

## 21. Content identity and manifests

### 21.1 Hash framing

All compound SHA-256 inputs use:

```text
frame(label, bytes) =
  u32be(length(label_utf8))
  || label_utf8
  || u64be(length(bytes))
  || bytes
```

Labels are ASCII and unique within each hash recipe.

### 21.2 Compiler-semantics ID

`language/semantics.toml` contains exactly:

```toml
spec = "lexlean/compiler-semantics/1"
language = "1.0"
project_schema = "lexlean/project/1"
lock_schema = "lexlean/lock/1"
lexicon_schema = "lexlean/lexicon/1"
entry_schema = "lexlean/entry/1"
lean_backend = "1"
latex_backend = "1"
proof_lowering = "1"
axiom_parser = "lean-4.32.1/1"
canonical_json = "1"
```

The compiler-semantics ID is the §11.5 tree digest of:

- every regular file under `language/`;
- every regular file under `schemas/`;
- committed axiom-output parser fixtures under `tests/golden/axiom-parser/`;
- committed canonical-JSON fixtures under `tests/golden/canonical-json/`.

The specification-link gate ensures these version declarations agree with this document. The digest excludes README prose, CI YAML, host binaries, timestamps, and generated build output.

The released binary embeds this ID. Repository tests recompute it and compare.

### 21.3 Source ID

The source ID is:

```text
SHA256(
  "lexlean-source-v1\0"
  || frame("project", canonical_project_toml_bytes)
  || frame("lock", canonical_lock_bytes)
  || for each selected module/import-closure source in sorted path order:
       frame("path", project_relative_path_utf8)
       || frame("source", normalized_source_bytes)
)
```

`build_root` is retained as its project-relative configured spelling. Absolute project location is excluded.

### 21.4 Semantic ID

The semantic ID is:

```text
SHA256(
  "lexlean-semantic-v1\0"
  || frame("compiler-semantics", compiler_semantics_digest_bytes)
  || frame("language", "1.0")
  || frame("toolchain", "leanprover/lean4:v4.32.1")
  || frame("linked-ir", canonical_linked_ir_json)
  || frame("lexicon-closure", canonical_linked_lexicon_json)
)
```

It is platform-independent. Display spellings, title/heading phrase IR, and proof IR are included because they affect canonical document output.

### 21.5 Build ID and layout

The build ID distinguishes different source/configuration identities that link to the same semantic object:

```text
SHA256(
  "lexlean-build-v1\0"
  || frame("source-id", source_id_bytes)
  || frame("semantic-id", semantic_id_bytes)
)
```

A successful build is published atomically at:

```text
.lexlean/build/<build-id>/
```

with:

```text
manifest.json
modules/<full-module-path>.lean
modules/<full-module-path>.tex
maps/<full-module-path>.map.json
coverage/<full-module-path>.coverage.json
lexicons/<source-module>.closure.json
```

Paths in manifests use `/` regardless of host OS.

### 21.6 Build manifest

`manifest.json` has:

```json
{
  "spec": "lexlean/build-manifest/1",
  "compiler": {
    "version": "1.0.0",
    "semantics_id": "..."
  },
  "language": "1.0",
  "project": "example-project",
  "source_id": "...",
  "semantic_id": "...",
  "build_id": "...",
  "lean_toolchain": "leanprover/lean4:v4.32.1",
  "selection": [],
  "modules": [],
  "inputs": [],
  "outputs": []
}
```

Each output row contains kind, project/build-relative path, byte length, and SHA-256. Rows sort by `(kind, path)`.

The manifest does not contain its own hash. A verification attestation records the exact manifest-file hash.

### 21.7 Canonical JSON

All normative JSON uses this restricted canonical form:

- UTF-8;
- no BOM;
- no floating-point numbers;
- no JSON `null`; optional fields are omitted;
- no duplicate keys;
- object keys sorted by UTF-8 bytes;
- arrays in specified semantic order;
- integers in shortest decimal form;
- strings use required JSON escapes and otherwise raw UTF-8;
- no insignificant whitespace;
- one final LF in the file;
- hash recipes over canonical payload omit the final file LF unless they explicitly hash file bytes.

### 21.8 Atomicity and concurrency

Mutating commands acquire an exclusive lock at:

```text
.lexlean/.lock
```

The lock file itself is regular and contains no semantic data.

Artifacts are written to a same-filesystem staging directory, fsynced where supported, and renamed only after all required files and hashes are complete. Existing content-addressed directories are reused only after every file validates against the new manifest; otherwise the command fails rather than overwriting unexplained bytes.

A failed command removes its staging tree and leaves no verified artifact.

---

## 22. Verification

### 22.1 Verification stages

`lexlean verify` performs exactly:

1. project/config/lock validation;
2. check and linked-IR construction;
3. deterministic build rendering;
4. Lean/Lake/leanchecker toolchain preflight;
5. Lake-workspace lock preflight;
6. external-interface probe generation and elaboration;
7. generated-module elaboration and `.olean` production;
8. separate-process `leanchecker` replay for every generated module;
9. axiom-audit module generation and execution;
10. exact axiom-output parsing;
11. per-declaration policy enforcement;
12. optional configured PDF rendering;
13. process-output normalization;
14. verification-attestation construction;
15. atomic publication.

No stage is optional. PDF is absent only when the project configuration has no PDF provider.

### 22.2 Lake-resolved execution

All Lean processes run with working directory equal to the configured Lake workspace and through the environment produced by:

```text
lake env <tool> <arguments...>
```

LexLean locates `lake` from the pinned toolchain, uses an absolute executable path, and verifies its version and digest.

Generated source and `.olean` roots are prepended to `LEAN_PATH` for the invocation. Source and output paths mirror module names, so Lean module discovery is deterministic.

LexLean does not run `lake update`, fetch dependencies, or modify the user's Lake files.

### 22.3 Module compilation

Modules compile in topological import order using the pinned `lean` executable. Each compilation emits:

- one `.olean`;
- captured normalized stdout;
- captured normalized stderr;
- exit status;
- process argv with normalized paths;
- executable digest.

LexLean does not request or include `.ilean`. Editor-information artifacts are not part of the normative proof artifact set.

Any nonzero exit, warning, unknown informational message, missing `.olean`, or output overflow fails verification.

### 22.4 `leanchecker`

For each generated module, sorted by full module name, LexLean invokes the pinned `leanchecker` in a separate process with that module prefix.

A zero exit is required. Normalized output is recorded.

This replay checks the newly loaded environment through Lean's kernel and is intended to detect environment manipulation. It is explicitly not described as an independent verifier.

### 22.5 Axiom output

With Lean 4.32.1, the accepted normalized payloads for one declaration are exactly:

```text
'<name>' does not depend on any axioms
```

or:

```text
'<name>' depends on axioms: [<comma-separated Lean names>]
```

The parser:

- accepts an optional Lean location/information envelope;
- requires the quoted declaration name to equal the expected full name;
- parses zero or one record per generated command and requires exactly one;
- trims only envelope whitespace;
- sorts and deduplicates the parsed axiom set, rejecting duplicate textual names;
- rejects any unrecognized payload;
- rejects missing or extra records.

Golden fixtures are taken from the pinned toolchain's `#print axioms` behavior.

### 22.6 Policy enforcement

For observed set `O` and configured set `A`:

- `none` succeeds iff `O = ∅`;
- `allow` succeeds iff `O ⊆ A`;
- `exact` succeeds iff `O = A`.

The attestation records policy, allowed set, observed set, and result for every declaration.

An imported theorem's axioms are not exempt because the theorem is upstream. If they flow into a generated declaration, the generated declaration's policy must permit them.

### 22.7 Process normalization

Before process output is hashed:

1. CRLF and CR become LF;
2. ANSI escape sequences are removed;
3. the longest matching absolute prefixes are replaced, in this order:
   - staging root → `$STAGING`;
   - project root → `$PROJECT`;
   - Lake workspace → `$LAKE_WORKSPACE`;
   - toolchain root → `$TOOLCHAIN`;
   - user home → `$HOME`;
4. trailing spaces are removed;
5. blank final lines collapse to one final LF.

Unexpected absolute paths remaining in successful normalized output fail attestation construction.

### 22.8 Verification layout

After success, the staging directory is renamed to:

```text
.lexlean/verified/<attestation-id>/
```

It contains:

```text
attestation.json
build-manifest.json
modules/*.lean
modules/*.tex
maps/*.map.json
coverage/*.coverage.json
lexicons/*.closure.json
oleans/*.olean
probe/<probe-module>.lean
probe/process.json
audit/<audit-module>.lean
audit/output.txt
audit/process.json
process/lean/*.json
process/leanchecker/*.json
pdf/*                                      # when configured
```

The artifact set is fixed. `verify` has no output-directory option and no option to omit maps, coverage, source, audit records, or process records.

### 22.9 Attestation ID

The attestation object contains `attestation_id`, but the ID is computed over the canonical object with that field removed:

```text
SHA256(
  "lexlean-attestation-v1\0"
  || frame("attestation-body", canonical_json(body_without_attestation_id))
)
```

The body records:

- build manifest bytes and SHA-256;
- semantic ID;
- host OS and architecture;
- LexLean version and executable hash;
- Lean, Lake, and leanchecker version output and executable hashes;
- Lake workspace lock hashes;
- every process record;
- generated `.olean` hashes;
- axiom policies and observed sets;
- optional PDF process and bytes;
- overall status exactly `verified`.

There is no timestamp in the hashed attestation. Digital signing is outside language 1.0; release automation may sign the completed file without changing its contents.

---

## 23. Command-line interface

### 23.1 General form

```text
lexlean [GLOBAL-OPTIONS] <COMMAND> [COMMAND-OPTIONS]
```

Global options:

```text
--project <path>                  default: lexlean.toml discovered upward
--diagnostic-format human|json    default: human
--color auto|always|never         default: auto; ignored for json
--version
--help
```

No environment variable changes semantic configuration.

### 23.2 Project discovery

Without `--project`, LexLean searches the current directory and parents for the first regular `lexlean.toml`. It stops at the filesystem root. Symlinked candidates are rejected.

The directory containing the selected config is the project root.

### 23.3 Selection

Commands accepting a selection support:

```text
--all
[INPUT...]
```

The modes are mutually exclusive:

- `--all`: every `.lex.tex` beneath every source root;
- one or more input paths: those modules and their transitive imports;
- neither: configured entrypoints and their transitive imports.

Inputs are project-relative or absolute paths that resolve beneath a configured source root. Duplicate logical modules, case-fold collisions, and two paths declaring the same module are errors.

Selections canonicalize to a sorted set. APIs and CLI results are always project result sets, even for one module.

### 23.4 Commands

#### `init`

```text
lexlean init [PATH] --name <name> --module-prefix <prefix>
```

Creates a new project only in an absent or empty directory. It writes canonical config, a canonical initial lock for builtin packages and workspace pins, `lean-toolchain`, a minimal Lake workspace, `src/Main.lex.tex`, and `.gitignore`. It never overwrites.

#### `lock`

```text
lexlean lock [--check] [--allow-network]
```

`--check` and `--allow-network` are mutually exclusive. Without either, it updates from local and cached exact sources. It writes atomically.

#### `check`

```text
lexlean check [--all | INPUT...]
```

Runs through linked IR and emits no build artifacts.

#### `build`

```text
lexlean build [--all | INPUT...]
```

Emits the fixed build layout at the build-ID path. It does not run Lean, does not invoke the PDF provider, and does not claim verification.

#### `verify`

```text
lexlean verify [--all | INPUT...]
```

Runs §22. It accepts no output or stage-suppression option.

#### `fmt`

```text
lexlean fmt [--check] [--all | INPUT...]
```

Parses and uniquely resolves source, rewrites canonical source, or exact-byte compares under `--check`.

#### `clean`

```text
lexlean clean
```

Removes only the configured `.lexlean` build root after verifying it is a nonsymlink directory inside the project. It does not remove package caches outside that root.

#### `explain`

```text
lexlean explain <DIAGNOSTIC-CODE>
```

Prints the generated `ERRORS.md` entry for one registered code. Unknown codes exit as CLI misuse.

### 23.5 Formatting

Canonical source formatting:

- NFC and LF;
- two spaces per environment nesting level;
- imports sorted;
- safe canonical lexical forms selected;
- explicit qualified selectors retained only when required for disambiguation;
- one structural control per line;
- one proposition or definition sentence per logical line;
- one proof sentence per line;
- axiom names sorted;
- no trailing whitespace;
- one final LF.

Formatting MUST preserve linked IR. The formatter compares pre- and post-render canonical IR and fails if they differ.

### 23.6 Exit codes

| Code | Meaning |
|---:|---|
| `0` | Command succeeded. |
| `1` | Source, glossary, grammar, semantic, Lean, proof, or axiom-policy failure. |
| `2` | CLI misuse, project-config error, lock-schema error, or invalid selection. |
| `3` | Missing or mismatched toolchain, Lake workspace, executable, or environment. |
| `4` | Security-policy or explicit resource-limit violation. |
| `70` | Internal invariant or software failure. |

A process terminated by the OS may additionally expose the platform's signal/exception status.

### 23.7 Output streams

Human mode:

- successful summaries to stdout;
- diagnostics to stderr;
- no progress spinner in noninteractive mode;
- paths project-relative where possible.

JSON mode:

- exactly one canonical JSON command-result object to stdout;
- stderr empty unless the process cannot construct JSON because of an internal failure;
- no color or progress text.

---

## 24. Public Rust API

### 24.1 Stable entry point

`crates/lexlean/src/lib.rs` exports:

```rust
pub struct Engine;
```

with:

```rust
impl Engine {
    pub fn load(project_file: &Utf8Path) -> Result<Self, LexLeanError>;
    pub fn lock(&self, request: LockRequest) -> Result<LockResult, LexLeanError>;
    pub fn check(&self, request: CheckRequest) -> Result<ProjectResultSet<CheckedUnit>, LexLeanError>;
    pub fn build(&self, request: BuildRequest) -> Result<ProjectResultSet<BuiltUnit>, LexLeanError>;
    pub fn verify(&self, request: VerifyRequest) -> Result<VerifiedProject, LexLeanError>;
    pub fn format(&self, request: FormatRequest) -> Result<FormatResultSet, LexLeanError>;
}
```

### 24.2 Selection type

```rust
pub enum Selection {
    Entrypoints,
    All,
    Files(BTreeSet<Utf8PathBuf>),
}
```

An empty `Files` set is invalid. No API treats a multi-module operation as singular.

### 24.3 Requests

```rust
pub struct CheckRequest {
    pub selection: Selection,
}

pub struct BuildRequest {
    pub selection: Selection,
}

pub struct VerifyRequest {
    pub selection: Selection,
}

pub struct FormatRequest {
    pub selection: Selection,
    pub check_only: bool,
}

pub struct LockRequest {
    pub check_only: bool,
    pub allow_network: bool,
}
```

Build and verify requests cannot alter artifact selection, backend, axiom audit, toolchain, limits, or PDF policy.

### 24.4 Result sets

```rust
pub struct ProjectResultSet<U> {
    pub source_id: Sha256Digest,
    pub semantic_id: Sha256Digest,
    pub build_id: Option<Sha256Digest>,
    pub units: BTreeMap<ModuleName, U>,
}

pub struct CheckedUnit {
    pub module: ModuleName,
    pub summary: CheckedUnitSummary,
}

pub struct BuiltUnit {
    pub module: ModuleName,
    pub artifacts: ModuleArtifacts,
}

pub struct VerifiedProject {
    pub source_id: Sha256Digest,
    pub semantic_id: Sha256Digest,
    pub build_id: Sha256Digest,
    pub attestation_id: Sha256Digest,
    pub root: Utf8PathBuf,
    pub units: BTreeMap<ModuleName, VerifiedUnit>,
}
```

The full mutable compiler IR remains internal. Stable serializable summaries and artifact schema types are public.

### 24.5 Errors

Every public function returns only `LexLeanError`:

```rust
pub struct LexLeanError {
    pub class: ErrorClass,
    pub diagnostics: Vec<Diagnostic>,
    pub source: Option<Box<dyn std::error::Error + Send + Sync>>,
}
```

`ErrorClass` is:

```rust
pub enum ErrorClass {
    Language,
    CliOrConfiguration,
    Environment,
    SecurityOrLimit,
    Internal,
}
```

It maps exactly to CLI exit codes 1, 2, 3, 4, and 70.

No public function panics for malformed user input, filesystem races, child failure, invalid UTF-8 input, invalid TOML/JSON, or unexpected external output.

---

## 25. Security and operational behavior

### 25.1 Filesystem confinement

LexLean:

- canonicalizes the project root once;
- rejects non-UTF-8 logical paths;
- rejects symlinks in source roots, lexicon packages, lock inputs, build roots, and declared PDF resources;
- rejects any normalized `..` escape;
- rejects duplicate files by filesystem identity;
- detects case-fold collisions before output;
- never follows a generated-output symlink;
- uses create-new semantics for staging files;
- validates existing content-addressed output before reuse.

### 25.2 No shell

Every child process is launched by executable path and argument vector. No command is passed through `sh`, `bash`, `cmd.exe`, PowerShell, or an equivalent shell.

### 25.3 No network

`check`, `build`, `fmt`, `verify`, `clean`, and `explain` do not invoke a network client. They do not update Lake or Git state.

Only `lock --allow-network` may acquire an exact configured Git commit over HTTPS. Prompts are disabled and mutable references are not accepted.

### 25.4 Child environment

Child environments begin from an allow-list required to locate the pinned toolchain and Lake workspace. LexLean explicitly sets:

```text
NO_COLOR=1
LANG=C.UTF-8
LC_ALL=C.UTF-8
GIT_TERMINAL_PROMPT=0
```

Platform-required path/home variables may be retained, normalized in records, and included in the environment preflight. Semantic configuration cannot be supplied through environment variables.

The PDF provider receives an isolated temporary home and no inherited proxy variables.

### 25.5 Limits

Every parser, token-lattice, graph, IR, diagnostic, child-output, and child-time limit is enforced with checked arithmetic. A limit failure is `LLS8002`, not an allocation panic.

### 25.6 Temporary data

Temporary directories are created beneath the configured build root with owner-only permissions where supported. They are removed on success and failure after atomic publication. LexLean does not print secret environment values or arbitrary file contents in diagnostics.

### 25.7 Internal invariants

An internal invariant failure:

- uses exit 70;
- emits `LLI9001`;
- identifies the phase and stable invariant name;
- does not claim a user source error;
- leaves no verified artifact.



## 26. Diagnostic registry and closed error model

### 26.1 `model/errors.toml`

Every public diagnostic code is registered once:

```toml
spec = "lexlean/errors/1"

[[error]]
code = "LLL1004"
class = "language"
exit = 1
title = "Unknown source atom"
statement = "A non-whitespace primitive atom has no covering lexical or scoped declaration."
```

Rows sort by code. Unknown fields, duplicate codes, invalid class/exit combinations, and an empty statement fail the model gate.

`ERRORS.md` is generated from this file. Source uses diagnostic codes only through a checked constructor or macro whose code argument is a compile-time string literal. `xtask` rejects a code used in Rust, tests, fixtures, or documentation that is absent from the registry, and rejects an unused registered code.

### 26.2 Code ranges

| Range | Class |
|---|---|
| `LLC0001`–`LLC0999` | CLI, configuration, selection, and lock structure |
| `LLL1001`–`LLL1999` | normalization, scanning, lexical closure, and token coverage |
| `LLP2001`–`LLP2999` | structural, phrase, mathematical, and proposition parsing |
| `LLR3001`–`LLR3999` | lexicon packages, references, imports, and resolution |
| `LLT4001`–`LLT4999` | conservative elaboration, signatures, and linking |
| `LLF5001`–`LLF5999` | definitions and structured proofs |
| `LLB6001`–`LLB6999` | Lean/LaTeX/PDF lowering and artifact construction |
| `LLV7001`–`LLV7999` | toolchain, Lean, replay, audit, and verification |
| `LLS8001`–`LLS8999` | filesystem security, networking, child policy, and limits |
| `LLI9001`–`LLI9999` | internal invariants |

### 26.3 Required diagnostic codes

The initial registry MUST include at least these exact codes and meanings:

| Code | Meaning |
|---|---|
| `LLC0001` | Invalid command-line usage. |
| `LLC0002` | Mutually exclusive or empty selection. |
| `LLC0101` | Invalid or unknown project configuration field. |
| `LLC0102` | Missing, stale, or noncanonical lock file. |
| `LLC0103` | Unsupported schema or language version. |
| `LLC0104` | Duplicate module or case-folded path collision. |
| `LLL1001` | Invalid UTF-8, forbidden scalar, or line-ending form. |
| `LLL1002` | Forbidden comment, raw percent, tab, or TeX escape. |
| `LLL1003` | Non-NFC or noncanonical source requiring formatting. |
| `LLL1004` | Unknown non-whitespace primitive atom. |
| `LLL1005` | Source token-coverage gap or overlap. |
| `LLL1006` | Token-lattice construction failure. |
| `LLP2001` | No grammar parse. |
| `LLP2002` | More than one distinct linked interpretation. |
| `LLP2003` | Invalid structural order or component cardinality. |
| `LLP2004` | Invalid math precedence, associativity, or grouping. |
| `LLR3001` | Missing package, version, source, or digest mismatch. |
| `LLR3002` | Duplicate package, entry, form, or qualified ID. |
| `LLR3003` | Import, denotation, module, or definition cycle. |
| `LLR3004` | Invalid LSE, LRE, frame, form, or renderer token. |
| `LLR3005` | Unavailable or invalid document/external reference. |
| `LLR3006` | Unsafe canonical form or raw renderer output. |
| `LLT4001` | Arity, binder, category, or conservative type mismatch. |
| `LLT4002` | Unresolved overloaded entry. |
| `LLT4003` | External-interface probe mismatch. |
| `LLT4004` | Document-entry signature mismatch. |
| `LLF5001` | Invalid definition form, self head, or recursion. |
| `LLF5002` | Invalid proof step for the current goal. |
| `LLF5003` | Missing, duplicate, or malformed proof branch. |
| `LLF5004` | Proof does not close all goals. |
| `LLF5005` | Forbidden proof form or proof hole. |
| `LLB6001` | Lean lowering has no defined form. |
| `LLB6002` | LaTeX lowering or renderer-token coverage failure. |
| `LLB6003` | Artifact hash, schema, or atomic publication failure. |
| `LLB6004` | PDF-provider protocol failure. |
| `LLV7001` | Lean/Lake/leanchecker version or executable mismatch. |
| `LLV7002` | Generated Lean elaboration or compilation failure. |
| `LLV7003` | `leanchecker` replay failure. |
| `LLV7004` | Missing, malformed, or unexpected axiom-audit output. |
| `LLV7005` | Axiom policy violation. |
| `LLV7006` | Lean warning or unexpected successful-process output. |
| `LLV7007` | Lake workspace lock or dependency availability mismatch. |
| `LLS8001` | Path escape, symlink, special file, or filesystem identity conflict. |
| `LLS8002` | Explicit project resource limit exceeded. |
| `LLS8003` | Network operation attempted outside permitted lock acquisition. |
| `LLS8004` | Child environment, executable, hash, or shell-policy violation. |
| `LLI9001` | Internal invariant failure. |

An implementation may add a more specific code only by adding the model row, scenario, test, generated documentation, and behavior in the same change.

---

## 27. Repository claim and gate model

### 27.1 Separation of models

`model/*.toml` records claims about the LexLean repository and implementation.

`language/` and lexicon packages define the language accepted by LexLean.

A user's mathematical declarations never become repository conformance IDs merely by being compiled. This separation is strict.

### 27.2 Repository rules

`AGENTS.md` MUST define these rules and remain the only repository file that assigns `R` numbers:

| Rule | Requirement |
|---|---|
| R1 | `model/*.toml` is the single source of every repository conformance claim and public diagnostic code; generated claim/error documentation must match. |
| R2 | Honesty levels are load-bearing: `some-true`, `build`, and `open` are never blurred. |
| R3 | A capability begins with a register row, then one scenario, then one failing named test, then implementation. |
| R4 | Nothing is deferred: no deferral marker, stub, placeholder component, empty branch, or feature switch that disables a normative capability. |
| R5 | Every public failure is registered and emitted through the closed error model; user input never panics. |
| R6 | Shipped dependency boundaries, versions, licenses, and sources are explicit and audited. |
| R7 | Every accepted LexLean source and canonical output satisfies complete lexical and symbolic closure. |
| R8 | Lean and LaTeX are both derived from one linked IR; neither backend may accept an opaque bypass. |
| R9 | Verified status requires Lean elaboration, kernel replay, exact axiom audit, and policy success. |
| R10 | Platform-independent artifacts are deterministic, source-mapped, and content-addressed. |

### 27.3 Honesty levels

The template levels retain their meanings:

- `some-true`: a fact reproduced from an authority and not established by this repository;
- `build`: behavior constructed here and validated against its oracle;
- `open`: measured and reported, never asserted as established.

Every LexLean capability ID in §31 is `build`.

The initial repository has no `open` implementation claim. An open research or performance measurement may be added only as a ledger row and must not be used as acceptance evidence.

### 27.4 Authorities

`model/authorities.toml` MUST initially identify:

| Authority ID | Subject |
|---|---|
| `LEAN-REL-4-32-1` | Lean 4.32.1 release/tag and source commit |
| `LAKE-4-32-1` | Lake distributed with Lean 4.32.1 |
| `LEANCHECKER-4-32-1` | `leanchecker` replay behavior and its stated non-independent status |
| `PRINT-AXIOMS-4-32-1` | Lean 4.32.1 `#print axioms` output behavior |

Corresponding ledger claims are `some-true`. LexLean tests realize compatibility with those authorities but do not re-register Lean's guarantees as LexLean proofs.

### 27.5 Generated documents

`cargo xtask validate-model` MUST:

1. parse all model files with unknown-field rejection;
2. validate IDs, levels, authorities, errors, and cross-references;
3. generate `CONFORMANCE.md` and `ERRORS.md` in memory;
4. compare exact committed bytes;
5. scan feature scenarios and Rust test names;
6. reject missing, duplicate, or extra links;
7. run the honesty vocabulary checks;
8. run repository-specific audits.

`model-write` is the only normal path that rewrites generated documentation.

### 27.6 Specification links

`cargo xtask validate-spec-links` parses the §31 table and requires:

- every table ID appears exactly once;
- every `model/ids.toml` ID appears exactly once in the table;
- suite and statement match the model row;
- all IDs are `build`;
- every source section referenced by an ID exists.

The conformance table is therefore a normative requirement index while the model remains the source of the repository's implemented-claim register.

### 27.7 Gherkin subset

The inherited deliberately small parser is retained. Each suite file contains:

- a `Feature:` heading for humans;
- one tag line `@<ID> @build`;
- one `Scenario:` line;
- one or more `Given`, `When`, `Then`, `And`, or `But` steps.

No background, outline, examples table, pending step, or alternate tag order is accepted.

Each ID has exactly one scenario. The scenario's statement must equal its model statement after trimming.

### 27.8 Test naming

For ID `LX-01`, the exact Rust test function name is:

```rust
fn conformance_lx_01()
```

This formula applies to every ID. The conformance meta-gate rejects:

- a registered ID with no such test;
- more than one test claiming the same ID;
- a scenario with no ID;
- a test naming an unregistered ID;
- a test ignored by `#[ignore]`;
- a test hidden behind a disabled feature.

### 27.9 Falsifiable gates

Every new gate must have a committed falsifiability record in `VERIFICATION.md` describing:

- planted defect;
- command run;
- expected failure;
- observed diagnostic;
- removal of defect.

A gate that cannot be falsified because the relevant register is empty must report that it is armed by the first row, not pass silently as evidence.

### 27.10 Repository audits

The template audits are adapted as follows:

- `audit-deferral` scans all Rust, TOML, JSON, Markdown, Gherkin, `.lex.tex`, language, schema, example, and xtask source outside generated output and dependency caches;
- marker strings are assembled in pieces in the gate so it can scan its own source;
- mentions inside Markdown code spans or fenced code are allowed;
- `audit-errors` checks every public diagnostic against `model/errors.toml`;
- `audit-shipped` derives shipped crates from `publish = false`;
- `audit-generated` proves generated documents and schemas are current;
- `audit-language-closure` checks built-in lexicons and renderer tokens;
- `audit-no-unsafe` verifies the shipped crate forbids unsafe code.

---

## 28. Testing strategy

### 28.1 Test classes

The repository MUST contain:

1. unit tests for scanners, parsers, LSE/LRE, IR, hashing, path rules, and output parsers;
2. property tests for normalization, canonical serialization, alpha-safe scope handling, and formatter idempotence;
3. golden tests for canonical `.lex.tex`, `.lean`, `.tex`, maps, coverage, manifests, diagnostics, and normalized process output;
4. integration tests invoking the public API;
5. CLI tests for every command and exit code;
6. conformance tests for every §31 ID;
7. positive end-to-end Lean verification fixtures;
8. negative fixtures for every rejection class;
9. two-directory reproducibility tests;
10. gate-falsifiability tests.

### 28.2 Fixture layout

```text
tests/fixtures/<suite>/<id>/
├── project/
├── expected/
│   ├── command.json
│   ├── diagnostics.json
│   ├── artifacts.json
│   └── hashes.toml
└── case.toml
```

`case.toml` contains:

```toml
spec = "lexlean/test-case/1"
command = "check"
args = []
expected_exit = 0
expect_artifacts = true
```

A fixture may contain multiple invocations only when its conformance statement explicitly concerns sequence behavior, such as stale-lock detection. Such a fixture uses sorted `[[invocation]]` rows.

Expected process-dependent hashes are stored separately from platform-independent golden hashes.

### 28.3 Golden updates

Golden output changes require:

- an explicit `just golden-write`;
- a reviewed diff;
- a compiler-semantics ID change when language or backend semantics changed;
- updated conformance evidence when behavior changed.

Tests MUST NOT automatically accept new output.

### 28.4 Reproducibility test

The reproducibility gate copies one project into two distinct absolute directories, runs a clean `build` in each, and compares:

- generated Lean;
- canonical LaTeX;
- source maps after required normalization;
- coverage;
- lexicon closure;
- build manifest.

Verified attestations and `.olean` files are excluded because they are platform/process-bound. Their own internal hashes and normalization are tested separately.

### 28.5 Negative requirements

Tests MUST establish that LexLean rejects, at minimum:

- one unknown word;
- one unknown symbol;
- one unknown control;
- raw percent comments;
- raw Lean;
- a TeX macro;
- ambiguous lexical segmentation;
- ambiguous typed resolution;
- missing glossary entry;
- lexicon cycle;
- unsafe renderer control;
- forward document reference;
- recursive definition;
- missing proof;
- extra proof branch;
- unrestricted simplify;
- `native_decide`;
- a Lean elaboration failure;
- a `leanchecker` failure fixture;
- malformed axiom output;
- an axiom-policy excess;
- a path symlink;
- a stale lock;
- a toolchain mismatch;
- a configured limit overrun;
- a PDF executable hash mismatch.

### 28.6 Example verification

Every directory under `examples/` is discovered rather than listed. Each example MUST include its lock and expected platform-independent build outputs. `cargo xtask verify-examples` runs `fmt --check`, `lock --check`, `check`, `build`, and `verify`.

---

## 29. Literal minimal example

### 29.1 Required standard Nat lexicon

`lexlean.std.nat@1.0.0` MUST provide at least:

| Entry | Category | Lean denotation | Canonical source |
|---|---|---|---|
| `nat` | `type-noun` | `Nat` | `natural number` / `natural numbers` |
| `zero` | `term-constant` | `Nat.zero` | `zero` and math `0` through numeral semantics |
| `succ` | `function` | `Nat.succ` | qualified/call form |
| `add` | `infix-function` | `Nat.add` | `+` |
| `addition` | `label-word` | a defined concept reference to `add` | `addition` |

It MUST include the Nat cases/induction descriptor.

### 29.2 Example files

`examples/nat-add-zero/lexlean.toml`:

```toml
spec = "lexlean/project/1"
name = "nat-add-zero"
language = "1.0"
module_prefix = "LexLeanExample"
source_roots = ["src"]
entrypoints = ["src/Main.lex.tex"]
build_root = ".lexlean"
lockfile = "lexlean.lock"
lean_workspace = "."
lean_toolchain = "leanprover/lean4:v4.32.1"

[[lexicon_source]]
package = "lexlean.std.nat"
kind = "builtin"

[limits]
max_file_bytes = 4194304
max_total_source_bytes = 67108864
max_primitive_atoms = 2000000
max_token_lattice_edges = 4000000
max_parse_states = 4000000
max_ir_nodes = 2000000
max_scope_depth = 1024
max_import_depth = 128
max_diagnostics = 256
max_child_output_bytes = 16777216
child_timeout_ms = 300000
```

`examples/nat-add-zero/lean-toolchain`:

```text
leanprover/lean4:v4.32.1
```

`examples/nat-add-zero/lakefile.toml`:

```toml
name = "nat_add_zero_host"
version = "0.1.0"
defaultTargets = ["NatAddZeroHost"]

[[lean_lib]]
name = "NatAddZeroHost"
```

`examples/nat-add-zero/NatAddZeroHost.lean`:

```lean
module
import Init
```

`examples/nat-add-zero/src/Main.lex.tex`:

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

`lexlean lock` generates and the repository commits the exact `lexlean.lock` for the built-in package and workspace files.

### 29.3 Expected generated Lean

The canonical generated module is exactly:

```lean
module
import Init
set_option autoImplicit false
namespace LexLeanExample.Main

theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by
  rfl

end LexLeanExample.Main
```

No prose or comments occur in the file.

### 29.4 Expected canonical LaTeX

The canonical `.tex` bytes are:

```latex
\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage[hidelinks]{hyperref}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\begin{document}
\begin{center}
{\LARGE Natural number addition}
\end{center}
\begin{theorem}
\label{ll:main:add-zero}
For every natural number \(n\), \(n + 0 = n\).
\end{theorem}
\begin{proof}
The goal follows by reflexivity.
\end{proof}
\end{document}
```

Every word, symbol, and control in this file has a coverage origin.

### 29.5 Expected verification

Verification MUST observe an empty axiom set for:

```text
LexLeanExample.Main.add_zero
```

The example's verified artifact is platform-bound. The committed example oracle contains platform-independent build artifacts and expected normalized verification records, not a cross-platform `.olean` oracle.

### 29.6 Required example mutations

The example suite MUST mechanically demonstrate:

1. changing `=` to a false proposition causes the old proof to fail in Lean;
2. replacing `addition` in the title with an undeclared word fails lexical closure;
3. adding a second same-surface proof entry with an indistinguishable signature causes ambiguity;
4. changing `\noaxioms` to an insufficient allow-list fails policy checking when a fixture introduces an axiom-dependent proof;
5. two clean builds in distinct paths are byte-identical for platform-independent artifacts.

---

## 30. Versioning, release, and completion

### 30.1 Version axes

LexLean has separate versions for:

- compiler crate/binary SemVer;
- language identifier `1.0`;
- project schema;
- lock schema;
- lexicon schema;
- entry schema;
- artifact schemas;
- compiler-semantics ID.

A compiler patch release may retain the semantics ID only when canonical accepted language, IR, diagnostics required for success/failure, and generated artifacts are unchanged.

### 30.2 Compatibility

Language 1.0 accepts only exact schema tags specified here. It does not silently interpret an unknown major or minor schema. A future compiler may support multiple versions through explicit dispatch, but a language-1.0 run remains byte-compatible.

No automatic in-place migration command is part of 1.0. Unsupported input fails with `LLC0103`.

### 30.3 Release artifacts

A `1.0.0` release MUST publish:

- source tag;
- checksums;
- supported-host binaries;
- crate package;
- compiler-semantics ID;
- generated `CONFORMANCE.md`;
- generated `ERRORS.md`;
- `SPEC.md`;
- license files;
- a software-bill-of-materials artifact;
- CI evidence that `just vv` passed on the tagged commit.

Release binaries MUST report:

```text
lexlean 1.0.0
language 1.0
compiler-semantics <digest>
lean-toolchain leanprover/lean4:v4.32.1
```

### 30.4 Completion criterion

The project is complete for LexLean 1.0 only when:

- every §31 ID is implemented at level `build`;
- no ID is represented by a stub or ignored test;
- all schemas are committed and exercised;
- built-in core, Nat, Int, and UOR Atlas lexicons validate;
- the literal example verifies;
- every negative fixture fails for the prescribed reason;
- every gate has falsifiability evidence;
- `just vv` passes from a clean checkout;
- the default branch has no `open` row used as a substitute for a capability;
- README claims are generated from or explicitly tied to model IDs;
- no normative behavior remains dependent on unspecified implementation choice.

### 30.5 Required implementation order

Each capability change follows R3. At repository scale, the dependency order is:

1. adapt template identity, rules, errors, and gates;
2. commit normative schemas and built-in language data;
3. implement normalization, scanning, package loading, and locking;
4. implement token lattice, structural grammar, expressions, and proposition grammar;
5. implement scope, resolution, conservative elaboration, linking, and IR;
6. implement definitions and proof IR;
7. implement canonical Lean, LaTeX, maps, coverage, and manifests;
8. implement toolchain preflight, external probes, Lean compilation, replay, and axiom audit;
9. implement CLI and stable Rust API;
10. complete examples, negative fixtures, reproducibility, and release gates.

The default branch must remain passing at each merge; a capability row is merged only with its complete scenario, test, implementation, and evidence.


## 31. Complete conformance-ID registry

Every row below is normative, has honesty level `build`, and MUST be copied byte-for-byte into `model/ids.toml` as its `statement`. The `suite` column names `features/suites/<suite>.feature`. The required Rust test name is `conformance_<id>` after lower-casing and replacing `-` with `_`.

| ID | Suite | Normative statement | Primary specification |
|---|---|---|---|
| `RP-01` | `repository` | The repository, crate, executable, metadata, and licenses have the exact LexLean identity specified. | §2 |
| `RP-02` | `repository` | The repository is derived from the pinned UOR template commit and contains no inherited domain-specific claim logic. | §2.2 |
| `RP-03` | `repository` | The completed repository has the required file and crate layout. | §7 |
| `RP-04` | `repository` | Only the lexlean crate is shipped and no shipped crate depends on repository-only tooling. | §7, §8.4 |
| `RP-05` | `repository` | The just vv recipe runs every normative acceptance gate in the specified order. | §9.2 |
| `RP-06` | `repository` | CONFORMANCE.md and ERRORS.md are exact generated views of model files. | §27.5 |
| `RP-07` | `repository` | The specification conformance table and model register are bijective and text-consistent. | §27.6 |
| `RP-08` | `repository` | Repository source contains no unsanctioned deferral marker, stub, placeholder, ignored capability, or disabling feature. | §27.10 |
| `RP-09` | `repository` | The shipped crate forbids unsafe Rust and the audit proves the prohibition is active. | §8.1, §27.10 |
| `RP-10` | `repository` | The embedded compiler-semantics ID equals a clean recomputation from normative language and schema inputs. | §21.2 |
| `RP-11` | `repository` | Every public README capability claim is tied to a registered model ID and honesty level. | §27 |
| `RP-12` | `repository` | A release is refused unless the complete release criterion and all required artifacts are satisfied. | §30 |
| `CF-01` | `configuration-lock` | Project configuration accepts exactly the project/1 schema and rejects unknown or missing fields. | §10.1 |
| `CF-02` | `configuration-lock` | Every operational limit is explicit, positive, parsed with checked arithmetic, and has no hidden default. | §10.2 |
| `CF-03` | `configuration-lock` | Configured paths resolve within the project under the specified UTF-8 and nonsymlink rules. | §10.1, §25.1 |
| `CF-04` | `configuration-lock` | Project discovery selects the nearest valid regular lexlean.toml and stops at the filesystem root. | §23.2 |
| `CF-05` | `configuration-lock` | Entrypoint, explicit-file, and all-module selections are mutually exclusive and canonicalized as specified. | §23.3 |
| `CF-06` | `configuration-lock` | Builtin, path, and exact-commit HTTPS Git lexicon sources obey their disjoint schemas. | §10.1 |
| `CF-07` | `configuration-lock` | The lock file is canonical, comment-free, sorted, generated, and exact-byte checkable. | §11 |
| `CF-08` | `configuration-lock` | The lock contains the complete exact transitive lexicon package closure including lexlean.core. | §11.3 |
| `CF-09` | `configuration-lock` | Package tree digests use the specified length-framed sorted-file algorithm and reject special files. | §11.5 |
| `CF-10` | `configuration-lock` | A changed config, package, workspace pin, or digest makes lock checking fail rather than silently refresh. | §11 |
| `CF-11` | `configuration-lock` | Check, build, format, and verify resolve only locked locally available dependencies. | §11.4 |
| `CF-12` | `configuration-lock` | Network package acquisition occurs only through lock --allow-network and only for an exact configured commit. | §11.4, §25.3 |
| `CF-13` | `configuration-lock` | The Lake workspace contains exactly one supported Lake configuration and the recorded workspace files match. | §10.4 |
| `CF-14` | `configuration-lock` | Language 1.0 accepts only leanprover/lean4:v4.32.1 for verification. | §8.2, §10.1 |
| `CF-15` | `configuration-lock` | Duplicate logical modules and case-folded path or module collisions are rejected. | §23.3 |
| `LX-01` | `lexical-closure` | Source decoding and line normalization enforce valid UTF-8, LF, final LF, and forbidden-scalar rules. | §12.1 |
| `LX-02` | `lexical-closure` | Non-NFC source is diagnosed and canonical formatting rewrites it without semantic change. | §12.1, §23.5 |
| `LX-03` | `lexical-closure` | Raw percent, comments, tabs, trailing spaces, and non-ASCII whitespace are rejected. | §12.1 |
| `LX-04` | `lexical-closure` | The primitive scanner recognizes exactly the specified atom classes and records exact spans. | §12.2 |
| `LX-05` | `lexical-closure` | Core braces, controls, punctuation, and grammar tokens receive glossary coverage rather than TeX trust. | §12.3 |
| `LX-06` | `lexical-closure` | An undeclared prose word is rejected with an exact unknown-atom diagnostic. | §14 |
| `LX-07` | `lexical-closure` | An undeclared symbol or control sequence is rejected with an exact unknown-atom diagnostic. | §14 |
| `LX-08` | `lexical-closure` | Lexical analysis builds all valid form edges without greedy import-order selection. | §14.1 |
| `LX-09` | `lexical-closure` | Every accepted non-whitespace source atom is covered exactly once in the selected path. | §6 I1, §14.1 |
| `LX-10` | `lexical-closure` | A local identifier is accepted only when introduced by a binder and every later occurrence resolves by scope. | §14.2 |
| `LX-11` | `lexical-closure` | TeX macro definition, expansion, file access, and execution controls are rejected even if a package declares them. | §12.4 |
| `LX-12` | `lexical-closure` | Qualified lexeme and document-reference controls select only existing closed entries or declarations. | §14.3 |
| `LX-13` | `lexical-closure` | Lexical or semantic ambiguity is rejected and no priority or heuristic chooses a candidate. | §14.4 |
| `LX-14` | `lexical-closure` | Canonical formatting chooses safe canonical forms and proves linked-IR preservation. | §23.5 |
| `GL-01` | `lexicon` | Lexicon packages obey the exact package layout, schema, ID-to-path rule, and exact imports. | §13.1 |
| `GL-02` | `lexicon` | Entry files obey the exact entry schema and category-specific field rules. | §13.2, §13.3 |
| `GL-03` | `lexicon` | Forms obey channel, feature, canonical-source, safety, and explicit-inflection requirements. | §13.5 |
| `GL-04` | `lexicon` | Every entry uses one fixed frame and packages cannot add grammar productions. | §13.4 |
| `GL-05` | `lexicon` | Denotations are exactly core, Lean, document, or acyclic defined values. | §13.6 |
| `GL-06` | `lexicon` | Every semantic entry has a valid canonical LSE signature with scoped binders and universes. | §13.7, §13.8 |
| `GL-07` | `lexicon` | Every canonical render uses valid LRE with complete slot use and no raw TeX. | §13.9 |
| `GL-08` | `lexicon` | Only the core renderer-token registry can authorize emitted LaTeX controls and glyphs. | §13.10 |
| `GL-09` | `lexicon` | Package import cycles and excessive import depth are rejected. | §13.11 |
| `GL-10` | `lexicon` | Defined-denotation cycles and document-definition cycles are rejected. | §13.6, §15.7 |
| `GL-11` | `lexicon` | A document denotation must resolve to an available declaration with a matching signature. | §13.6, §17.7 |
| `GL-12` | `lexicon` | Every used external Lean entry is checked by a generated interface probe during verification. | §18.8 |
| `GL-13` | `lexicon` | Duplicate packages, entries, forms, and qualified IDs are rejected while same-surface overloads remain explicit candidates. | §13.11, §14 |
| `GL-14` | `lexicon` | Cases and induction are available only through a complete validated eliminator descriptor. | §16.11 |
| `GL-15` | `lexicon` | Glossary files reject free description, documentation, note, meaning, and unknown prose fields. | §13.6 |
| `GL-16` | `lexicon` | Package and entry bytes participate in lock and semantic closure hashes exactly as specified. | §11, §21 |
| `GR-01` | `grammar` | A source module parses only under the exact structural grammar and environment set. | §15.1, §15.2 |
| `GR-02` | `grammar` | Glossary imports, module imports, title, and blocks obey exact header order and cardinality. | §15.1 |
| `GR-03` | `grammar` | Sections nest within the configured scope limit and section parameters introduce explicit inherited context. | §15.1, §15.4 |
| `GR-04` | `grammar` | Titles and headings accept only bounded concept phrases and cannot encode an unproved proposition. | §15.3 |
| `GR-05` | `grammar` | Only parenthesized and display control delimiters create math islands; dollar math is rejected. | §15.5 |
| `GR-06` | `grammar` | Dynamic mathematical operators obey declared precedence, associativity, and explicit grouping. | §15.5 |
| `GR-07` | `grammar` | Mathematical juxtaposition is never interpreted as implicit multiplication or application. | §15.5 |
| `GR-08` | `grammar` | Universal, existential, unique-existential, conditional, and connective proposition forms have the specified compositional semantics. | §15.6 |
| `GR-09` | `grammar` | Proposition precedence and associativity produce the specified parse or an ambiguity error. | §15.6 |
| `GR-10` | `grammar` | Articles, plural forms, capitalization, and inflections are explicit lexicon data rather than inferred language rules. | §13.5, §15.6 |
| `GR-11` | `grammar` | A component with no complete grammar parse fails with a bounded structured diagnostic. | §6 I3, §26 |
| `GR-12` | `grammar` | Distinct surviving parses fail as ambiguity while semantically identical canonical IR alternatives collapse. | §14.4 |
| `GR-13` | `grammar` | Free expository paragraphs and opaque text nodes are rejected. | §4.2, §15 |
| `GR-14` | `grammar` | Definition and theorem-like components enforce exact sentence, policy, and proof cardinalities. | §15.7, §15.8 |
| `GR-15` | `grammar` | Explicit module imports form an acyclic graph and selected builds include their transitive closure. | §15.1 |
| `GR-16` | `grammar` | A same-module declaration cannot reference a later declaration. | §15.1, §17.7 |
| `SM-01` | `semantic-ir` | Compiler phases execute in the required order and no backend receives an unlinked or ambiguous program. | §17.1 |
| `SM-02` | `semantic-ir` | Every global and local reference has one closed typed reference variant and one stable identity. | §17.2 |
| `SM-03` | `semantic-ir` | Term IR contains only the specified closed variants and represents every accepted semantic term. | §17.3 |
| `SM-04` | `semantic-ir` | Proof IR contains only the specified closed variants and represents every accepted proof form. | §17.4 |
| `SM-05` | `semantic-ir` | Conservative signature elaboration checks arity, binders, categories, and expected types without claiming Lean kernel equivalence. | §17.6 |
| `SM-06` | `semantic-ir` | Omitted implicit binders are recorded as controlled application metadata and user holes are rejected. | §17.3, §17.6 |
| `SM-07` | `semantic-ir` | Document-entry signatures and generated declaration signatures are compared canonically before rendering. | §17.7 |
| `SM-08` | `semantic-ir` | Module, component, local, and hypothesis name generation is deterministic and collision checked. | §17.8 |
| `SM-09` | `semantic-ir` | Linked IR has stable schema-tagged canonical JSON with alpha-safe binder serialization. | §17.9 |
| `SM-10` | `semantic-ir` | Source ID and semantic ID use exactly the specified framed hash inputs. | §21.3, §21.4 |
| `SM-11` | `semantic-ir` | Linked project result sets contain every selected module and imported module exactly once in stable order. | §17.5, §23.3 |
| `SM-12` | `semantic-ir` | No semantic IR node can contain opaque prose, raw backend text, or an unknown extension. | §6 I4, §17 |
| `SM-13` | `semantic-ir` | Inherited section parameters are represented explicitly and emitted only on declarations that use them. | §17.5, §18.3 |
| `SM-14` | `semantic-ir` | A numeral without a unique expected type is rejected rather than defaulted. | §15.5 |
| `DF-01` | `declarations` | A valid type-definition sentence emits one nonrecursive sort-valued Lean def linked to its document entry. | §15.7, §18.6 |
| `DF-02` | `declarations` | A valid term-definition sentence emits one nonrecursive explicitly typed Lean def. | §15.7, §18.6 |
| `DF-03` | `declarations` | A valid predicate-definition sentence emits one nonrecursive Prop-valued Lean def. | §15.7, §18.6 |
| `DF-04` | `declarations` | Self recursion, mutual recursion, and later-declaration references are rejected. | §15.7 |
| `DF-05` | `declarations` | A definition's self head, explicit arguments, and signature order are checked exactly. | §15.7 |
| `DF-06` | `declarations` | Every generated definition and theorem-like declaration carries one explicit axiom policy. | §15.9, §22.6 |
| `DF-07` | `declarations` | Theorem, lemma, and corollary each emit Lean theorem declarations while retaining distinct document metadata. | §15.8, §18.6 |
| `DF-08` | `declarations` | Author-defined axioms, opaque declarations, and proofless theorem-like components are rejected. | §4.2, §15.8 |
| `DF-09` | `declarations` | Every theorem-like component contains exactly one nonempty structured proof. | §15.8, §16 |
| `DF-10` | `declarations` | Generated declarations preserve source order and every document reference respects that order. | §18.3 |
| `PF-01` | `proofs` | Assume and exact-style simple proof sentences create scoped introductions and exact proof nodes. | §16.2 |
| `PF-02` | `proofs` | Simple Apply is accepted only when its declared signature yields exactly one residual premise. | §16.2 |
| `PF-03` | `proofs` | Structured apply requires every numbered residual premise exactly once and in signature order. | §16.6 |
| `PF-04` | `proofs` | Reflexivity lowers only to pinned Lean rfl and closes the current goal. | §16.2 |
| `PF-05` | `proofs` | Witness steps supply the next existential witness with no implicit search. | §16.2 |
| `PF-06` | `proofs` | Left and right alternative steps select only the corresponding disjunction constructor. | §16.2 |
| `PF-07` | `proofs` | Have establishes a nested proposition before introducing its fresh hypothesis into subsequent scope. | §16.3 |
| `PF-08` | `proofs` | Rewrite applies every explicitly directed rule strictly in source order at exactly one target. | §16.4 |
| `PF-09` | `proofs` | Simplify lowers to simp only with exactly the listed rules and target. | §16.5 |
| `PF-10` | `proofs` | Constructor requires the exact ordered branch count and every branch closes. | §16.7 |
| `PF-11` | `proofs` | Cases requires a validated descriptor, every constructor once, and exact branch binders. | §16.8 |
| `PF-12` | `proofs` | Induction requires a validated descriptor, every constructor once, and exact field and induction-hypothesis binders. | §16.9 |
| `PF-13` | `proofs` | Calculation chains use one declared relation, at least one step, and exact endpoint proofs. | §16.10 |
| `PF-14` | `proofs` | Proof locals, hypotheses, premise scopes, and case scopes cannot capture or leak. | §14.2, §16 |
| `PF-15` | `proofs` | Every proof and nested branch must close all goals and rejects steps after closure. | §16.1 |
| `PF-16` | `proofs` | Raw tactics, custom proof nodes, unrestricted automation, and proof holes are rejected. | §16.12 |
| `PF-17` | `proofs` | native_decide is never accepted or generated. | §16.12, §18.2 |
| `PF-18` | `proofs` | Lean proof failures remap to the smallest originating LexLean proof or statement span. | §20.4 |
| `LN-01` | `lean-backend` | Each generated Lean file has the exact module, import, option, namespace, declaration, and end structure. | §18.1 |
| `LN-02` | `lean-backend` | Imports are explicit, deduplicated, sorted, and every external global is fully qualified. | §18.3 |
| `LN-03` | `lean-backend` | Generated Lean contains no comments, documentation, strings, or copied source prose. | §18.2 |
| `LN-04` | `lean-backend` | Generated Lean contains no sorry, admit, axiom, opaque, unsafe, native_decide, or placeholder declaration. | §18.2 |
| `LN-05` | `lean-backend` | Every linked term and proof variant has one defined Lean lowering and missing lowering is a hard error. | §18.4, §18.7 |
| `LN-06` | `lean-backend` | Leading universal binders become deterministic declaration parameters with complete source mapping. | §18.5 |
| `LN-07` | `lean-backend` | All document definitions emit def and never alternate declaration forms. | §18.6 |
| `LN-08` | `lean-backend` | Proof lowering uses only the fixed pinned Lean forms enumerated by the specification. | §18.7 |
| `LN-09` | `lean-backend` | Lean formatting is byte-deterministic with fixed indentation, LF, and final LF. | §18 |
| `LN-10` | `lean-backend` | Every non-whitespace generated Lean token has a source, glossary, IR, or synthetic-core mapping. | §20.3 |
| `LN-11` | `lean-backend` | The generated-source audit tokenizes and rejects prose-bearing or forbidden Lean tokens before verification. | §18.2 |
| `LN-12` | `lean-backend` | Generated file paths and module names exactly mirror the configured module prefix and source module. | §15.1, §18.1 |
| `TX-01` | `latex-pdf` | Canonical LaTeX is rendered solely from linked IR and never copies source text or controls. | §19.1 |
| `TX-02` | `latex-pdf` | Every module uses the exact canonical LaTeX preamble and no host or timestamp metadata. | §19.2 |
| `TX-03` | `latex-pdf` | Statements use only canonical controlled proposition and definition renderings. | §19.3, §19.4 |
| `TX-04` | `latex-pdf` | Proof prose is generated from proof IR using fixed core lexical forms. | §19.5 |
| `TX-05` | `latex-pdf` | Titles, sections, parameters, environments, numbering, and labels follow the exact document rules. | §19.3 |
| `TX-06` | `latex-pdf` | Every visible LaTeX word, symbol, punctuation mark, and control has complete coverage. | §19.6 |
| `TX-07` | `latex-pdf` | Non-core lexicons cannot inject a raw TeX control or unclassified output segment. | §13.9, §19.6 |
| `TX-08` | `latex-pdf` | Canonical LaTeX bytes are deterministic, LF-normalized, and final-LF terminated. | §19 |
| `TX-09` | `latex-pdf` | An enabled external PDF provider runs without a shell in an isolated directory with exact hashes and resources. | §19.7 |
| `TX-10` | `latex-pdf` | The PDF recipe ID and actual PDF hash use the specified independent content records. | §19.8 |
| `TX-11` | `latex-pdf` | PDF success or failure never changes mathematical verification authority. | §19.7 |
| `TX-12` | `latex-pdf` | The publishable document is the canonical renderer output rather than unchecked source bytes. | §6 I8, §19 |
| `AR-01` | `artifacts` | Diagnostics use the canonical schema, exact spans, stable sorting, and registered codes. | §20.1, §26 |
| `AR-02` | `artifacts` | Source maps contain complete module, source, artifact, node, and range records. | §20.3 |
| `AR-03` | `artifacts` | Lean diagnostics remap by the specified smallest-enclosing mapping algorithm. | §20.4 |
| `AR-04` | `artifacts` | Coverage files record every required source and output token with no gap or overlap. | §20.5 |
| `AR-05` | `artifacts` | All compound hashes use the specified length-prefixed frame function. | §21.1 |
| `AR-06` | `artifacts` | Compiler-semantics identity is recomputed from the exact normative language, schema, backend, and parser inputs. | §21.2 |
| `AR-07` | `artifacts` | Source IDs are independent of absolute checkout location and include exact normalized inputs. | §21.3 |
| `AR-08` | `artifacts` | Semantic IDs are platform independent and include linked IR, lexicon closure, language semantics, and toolchain ID. | §21.4 |
| `AR-09` | `artifacts` | Successful builds publish only the fixed content-addressed build-ID layout. | §21.5 |
| `AR-10` | `artifacts` | Build manifests enumerate every input and output with stable paths, sizes, and hashes. | §21.6 |
| `AR-11` | `artifacts` | Normative JSON obeys the restricted canonical JSON format and hash/file newline distinction. | §21.7 |
| `AR-12` | `artifacts` | Concurrent and failed builds preserve atomic content-addressed artifacts and never overwrite unexplained bytes. | §21.8 |
| `AR-13` | `artifacts` | Two clean builds in different absolute directories produce byte-identical platform-independent artifacts. | §28.4 |
| `AR-14` | `artifacts` | Platform-independent build evidence is distinguished from platform-bound oleans, process records, PDF bytes, and attestations. | §21, §22 |
| `VR-01` | `verification` | Verification runs every specified stage in order and exposes no stage-suppression option. | §22.1 |
| `VR-02` | `verification` | Lean, Lake, and leanchecker versions and executable hashes are checked and recorded before use. | §22.2 |
| `VR-03` | `verification` | Lean execution uses the pinned Lake environment and never updates or fetches workspace dependencies. | §22.2 |
| `VR-04` | `verification` | Every used external interface is elaborated in the unique reserved probe module. | §18.8, §22.1 |
| `VR-05` | `verification` | Generated modules compile in topological order and produce one required olean each. | §22.3 |
| `VR-06` | `verification` | Verification neither requests nor includes ilean artifacts. | §22.3 |
| `VR-07` | `verification` | A Lean warning, unknown informational message, overflow, or missing output fails verification. | §20.2, §22.3 |
| `VR-08` | `verification` | Every generated module is replayed by a separate leanchecker process and every replay must succeed. | §22.4 |
| `VR-09` | `verification` | The unique reserved audit module prints axioms for every generated declaration exactly once. | §18.9 |
| `VR-10` | `verification` | The axiom parser accepts only the pinned exact output forms and rejects missing, duplicate, extra, or malformed records. | §22.5 |
| `VR-11` | `verification` | None, allow-subset, and exact axiom policies are enforced exactly and recorded per declaration. | §22.6 |
| `VR-12` | `verification` | Child process output is normalized with the exact path and line rules before hashing. | §22.7 |
| `VR-13` | `verification` | A verified directory contains the complete fixed source, map, coverage, olean, probe, audit, and process artifact set. | §22.8 |
| `VR-14` | `verification` | The attestation ID is computed over the canonical body with its ID field removed. | §22.9 |
| `VR-15` | `verification` | Any failed verification stage removes staging and produces no verified artifact or verified status. | §6 I11, §22 |
| `VR-16` | `verification` | Axioms flowing from imported theorems remain subject to the generated declaration's policy. | §22.6 |
| `VR-17` | `verification` | Lean workspace configuration and manifest hashes must match the lock and all dependencies must be locally available. | §10.4, §22.2 |
| `VR-18` | `verification` | Check and build results never claim verified or kernel-checked status. | §5.3 |
| `VR-19` | `verification` | The vendored Atlas library elaborates under the pinned toolchain and no declaration in it depends on an axiom outside Lean's own. | §10.4, §22.2, §22.6 |
| `CL-01` | `cli-api` | Global options and upward project discovery obey the exact CLI contract. | §23.1, §23.2 |
| `CL-02` | `cli-api` | Init creates the complete canonical skeleton only in an absent or empty destination and never overwrites. | §23.4 |
| `CL-03` | `cli-api` | Lock check, local update, and explicit network acquisition obey their exact mutually exclusive behavior. | §23.4 |
| `CL-04` | `cli-api` | Check runs through linked IR and emits no build artifacts. | §23.4 |
| `CL-05` | `cli-api` | Build emits the fixed build-ID artifact set without running Lean or claiming verification. | §23.4 |
| `CL-06` | `cli-api` | Verify runs the complete fixed verification pipeline and accepts no output or suppression option. | §23.4 |
| `CL-07` | `cli-api` | Format and format-check are idempotent and preserve linked IR. | §23.4, §23.5 |
| `CL-08` | `cli-api` | Clean removes only the validated configured build root and no source or external cache. | §23.4 |
| `CL-09` | `cli-api` | Explain prints exactly one registered diagnostic entry and rejects unknown codes. | §23.4 |
| `CL-10` | `cli-api` | All, explicit-files, and entrypoint selections return sorted project result sets including import closure. | §23.3 |
| `CL-11` | `cli-api` | Every command maps failures to the exact documented exit code. | §23.6 |
| `CL-12` | `cli-api` | Human and canonical-JSON output modes obey exact stream, color, and cardinality rules. | §23.7 |
| `CL-13` | `cli-api` | The public Engine exposes exactly the stable load, lock, check, build, verify, and format entry points. | §24.1 |
| `CL-14` | `cli-api` | Every public multi-module operation returns a ProjectResultSet or VerifiedProject rather than a singular unit. | §24.2, §24.4 |
| `CL-15` | `cli-api` | Public requests cannot override backends, toolchain, verification stages, limits, policies, or fixed artifact sets. | §24.3 |
| `CL-16` | `cli-api` | Every public failure is a LexLeanError and malformed user input cannot panic. | §24.5 |
| `CL-17` | `cli-api` | Environment variables cannot alter semantic project configuration. | §23.1, §25.4 |
| `CL-18` | `cli-api` | Version output reports compiler, language, semantics ID, and Lean toolchain exactly. | §30.3 |
| `SE-01` | `security` | Source, package, workspace, resource, and output paths are confined and symlinks are rejected. | §25.1 |
| `SE-02` | `security` | Special files, duplicate filesystem identities, and case-fold collisions are rejected before processing. | §25.1 |
| `SE-03` | `security` | All child processes use direct executable and argv invocation with no shell. | §25.2 |
| `SE-04` | `security` | No command except lock --allow-network may perform package network acquisition. | §25.3 |
| `SE-05` | `security` | Child environments use the specified deterministic allow-list and recorded normalization. | §25.4 |
| `SE-06` | `security` | Every configured parser, graph, IR, diagnostic, child-output, and timeout limit is enforced with checked arithmetic. | §25.5 |
| `SE-07` | `security` | Temporary data uses confined owner-only staging and is removed after atomic publication or failure. | §25.6 |
| `SE-08` | `security` | External executables and PDF resources are hash-checked before use. | §19.7, §22.2 |
| `SE-09` | `security` | PDF execution receives only canonical TeX and declared resources in an isolated working directory. | §19.7 |
| `SE-10` | `security` | Internal invariant failures use LLI9001 and exit 70 without misclassifying user input. | §25.7 |
| `SE-11` | `security` | Diagnostics and process records do not expose secret environment values or arbitrary unrelated file contents. | §25.6 |
| `SE-12` | `security` | Git lexicon acquisition accepts only an exact 40-hex commit over HTTPS and rejects submodules and LFS indirection. | §10.1, §11.4 |
| `EX-01` | `examples` | The committed nat-add-zero example formats, locks, checks, builds, and verifies with an empty axiom set. | §29 |
| `EX-02` | `examples` | Changing the example proposition while retaining the old proof causes remapped Lean verification failure. | §29.6 |
| `EX-03` | `examples` | Replacing a title concept with an undeclared word causes lexical-closure failure. | §29.6 |
| `EX-04` | `examples` | Adding an indistinguishable same-surface entry causes ambiguity rather than priority selection. | §29.6 |
| `EX-05` | `examples` | An axiom-dependent fixture fails an insufficient declaration policy and records the observed excess. | §29.6 |
| `EX-06` | `examples` | Two clean example builds in distinct paths have byte-identical platform-independent artifacts. | §29.6 |
| `EX-07` | `examples` | The negative fixture suite covers every required rejection class and prescribed diagnostic family. | §28.5 |
| `EX-08` | `examples` | Every example directory is discovered automatically and must satisfy the full example gate. | §28.6 |

**Total required capability IDs:** 210.

No row may be downgraded to `some-true` or `open`. Upstream Lean facts are ledger/authority rows, not substitutions for these build behaviors.

---

## 32. Final acceptance statement

A repository conforming to this specification has no semantically untracked prose path in a LexLean document:

- source tokens are closed;
- grammar is closed;
- denotations are closed;
- proof forms are closed;
- generated Lean is prose-free;
- generated LaTeX is coverage-complete;
- generation is deterministic;
- verification is explicit and kernel-backed;
- axiom dependencies are per-declaration and machine-audited;
- every public capability and failure is registered and falsifiable.

Accordingly, a change to the mathematical meaning changes the linked semantic object, the generated Lean statement, the canonical human document, or all three. A proof that no longer establishes the changed statement fails verification. There is no independent prose channel that can silently remain stale.