Feature: repository

  Repository identity, layout, gates, and generated-document discipline (§2, §7, §9, §27, §30).

  @RP-01 @build
  Scenario: The repository, crate, executable, metadata, and licenses have the exact LexLean identity specified.
    Given the workspace Cargo.toml, the lexlean crate manifest, and the two license files
    When the section 2.3 metadata rows and the exact one-line crate description are looked up and `lexlean --version` runs
    Then Cargo.toml contains version 0.1.1, edition 2021, rust-version 1.97, and license MIT OR Apache-2.0
    And LICENSE-APACHE and LICENSE-MIT exist as files
    And the binary prints `lexlean 0.1.1` on its first stdout line with exit 0

  @RP-02 @build
  Scenario: The repository is derived from the pinned UOR template commit and contains no inherited domain-specific claim logic.
    Given AGENTS.md, SPEC.md, xtask/src/audit.rs, xtask/src/main.rs, and the Justfile
    When the pinned template commit 0a1c799338d7db829aa23365e1acf4f9d01ff8b5 is searched for
    Then AGENTS.md and SPEC.md both record that commit
    And none of the four tooling files still mentions the template's audit-limits remnant

  @RP-03 @build
  Scenario: The completed repository has the required file and crate layout.
    Given the section 7 layout tree parsed out of the SPEC.md text fence
    When every tree row is resolved to a path under the repository root
    Then each row ending in a slash exists as a directory and every other row exists as a file
    And more than 80 rows were checked

  @RP-04 @build
  Scenario: Only the lexlean crate is shipped and no shipped crate depends on repository-only tooling.
    Given the Cargo.toml manifests of crates/model, crates/conformance, xtask, and crates/lexlean
    When each manifest is inspected for `publish = false` and dependency names
    Then the three tooling crates declare `publish = false` and the lexlean crate does not
    And the lexlean manifest names none of repo-model, repo-conformance, or xtask

  @RP-05 @build
  Scenario: The just vv recipe runs every normative acceptance gate in the specified order.
    Given the committed Justfile
    When the vv recipe line is read
    Then it reads `vv: fmt-check model spec-links lint test features bdd examples golden repro deny`
    And the Justfile also defines the model-write and golden-write recipes plus each of the eleven gates

  @RP-06 @build
  Scenario: CONFORMANCE.md and ERRORS.md are exact generated views of model files.
    Given the model directory loaded through repo_model::Model::load
    When CONFORMANCE.md and ERRORS.md are re-rendered from the loaded model in memory
    Then the committed CONFORMANCE.md is byte-equal to the rendered conformance view
    And the committed ERRORS.md is byte-equal to the rendered errors view

  @RP-07 @build
  Scenario: The specification conformance table and model register are bijective and text-consistent.
    Given the section 31 table of SPEC.md parsed into id, suite, and statement rows
    When the table is zipped against the model ids register in order
    Then both hold exactly 210 rows
    And each row's ID, suite, and statement text is equal in the table and the register

  @RP-08 @build
  Scenario: Repository source contains no unsanctioned deferral marker, stub, placeholder, ignored capability, or disabling feature.
    Given every rs, toml, json, feature, tex, and lean file outside target, .git, .lexlean, and expected directories
    When each file is scanned for the sanctioned list of deferral marker spellings, ignore attributes, and deferral macro calls
    Then no scanned file contains any marker
    And more than 100 files were scanned

  @RP-09 @build
  Scenario: The shipped crate forbids unsafe Rust and the audit proves the prohibition is active.
    Given crates/lexlean/src/lib.rs and every file under crates/lexlean/src
    When lib.rs is checked for the forbid unsafe-code crate attribute and every source is scanned for an unsafe keyword
    Then the forbid attribute is present in lib.rs
    And no shipped source file contains the unsafe token

  @RP-10 @build
  Scenario: The embedded compiler-semantics ID equals a clean recomputation from normative language and schema inputs.
    Given every file under language, schemas, tests/golden/axiom-parser, and tests/golden/canonical-json sorted by path bytes
    When lexlean::artifact::content_id::tree_digest recomputes the tree digest from those files
    Then the recomputed digest equals lexlean::compiler_semantics_id()

  @RP-11 @build
  Scenario: Every public README capability claim is tied to a registered model ID and honesty level.
    Given README.md and the loaded model ids register
    When every README table row marked `build` has its five-character IDs extracted
    Then each extracted ID is registered in the model at level build
    And at least 10 such capability rows are found

  @RP-12 @build
  Scenario: A release is refused unless the complete release criterion and all required artifacts are satisfied.
    Given the repository tree at version 0.1.1 and the repo_model::release CRITERIA list
    When repo_model::release::check runs against the tree
    Then release is refused and one refusal reason names source-tag
    And the criteria include source-tag, checksums, host-binaries, crate-package, semantics-id, conformance-doc, errors-doc, spec, licenses, sbom, and ci-evidence
    And the Justfile release recipe depends on vv and runs `cargo xtask release-check`
