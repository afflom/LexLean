Feature: repository

  Repository identity, layout, gates, and generated-document discipline (§2, §7, §9, §27, §30).

  @RP-01 @build
  Scenario: The repository, crate, executable, metadata, and licenses have the exact LexLean identity specified.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_01 exercises RP-01
    Then the observed behavior matches the registered statement exactly

  @RP-02 @build
  Scenario: The repository is derived from the pinned UOR template commit and contains no inherited domain-specific claim logic.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_02 exercises RP-02
    Then the observed behavior matches the registered statement exactly

  @RP-03 @build
  Scenario: The completed repository has the required file and crate layout.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_03 exercises RP-03
    Then the observed behavior matches the registered statement exactly

  @RP-04 @build
  Scenario: Only the lexlean crate is shipped and no shipped crate depends on repository-only tooling.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_04 exercises RP-04
    Then the observed behavior matches the registered statement exactly

  @RP-05 @build
  Scenario: The just vv recipe runs every normative acceptance gate in the specified order.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_05 exercises RP-05
    Then the observed behavior matches the registered statement exactly

  @RP-06 @build
  Scenario: CONFORMANCE.md and ERRORS.md are exact generated views of model files.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_06 exercises RP-06
    Then the observed behavior matches the registered statement exactly

  @RP-07 @build
  Scenario: The specification conformance table and model register are bijective and text-consistent.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_07 exercises RP-07
    Then the observed behavior matches the registered statement exactly

  @RP-08 @build
  Scenario: Repository source contains no unsanctioned deferral marker, stub, placeholder, ignored capability, or disabling feature.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_08 exercises RP-08
    Then the observed behavior matches the registered statement exactly

  @RP-09 @build
  Scenario: The shipped crate forbids unsafe Rust and the audit proves the prohibition is active.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_09 exercises RP-09
    Then the observed behavior matches the registered statement exactly

  @RP-10 @build
  Scenario: The embedded compiler-semantics ID equals a clean recomputation from normative language and schema inputs.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_10 exercises RP-10
    Then the observed behavior matches the registered statement exactly

  @RP-11 @build
  Scenario: Every public README capability claim is tied to a registered model ID and honesty level.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_11 exercises RP-11
    Then the observed behavior matches the registered statement exactly

  @RP-12 @build
  Scenario: A release is refused unless the complete release criterion and all required artifacts are satisfied.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_rp_12 exercises RP-12
    Then the observed behavior matches the registered statement exactly
