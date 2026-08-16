Feature: verification

  The fixed verification pipeline, replay, axiom audit, and attestations (§22).

  @VR-01 @build
  Scenario: Verification runs every specified stage in order and exposes no stage-suppression option.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_01 exercises VR-01
    Then the observed behavior matches the registered statement exactly

  @VR-02 @build
  Scenario: Lean, Lake, and leanchecker versions and executable hashes are checked and recorded before use.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_02 exercises VR-02
    Then the observed behavior matches the registered statement exactly

  @VR-03 @build
  Scenario: Lean execution uses the pinned Lake environment and never updates or fetches workspace dependencies.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_03 exercises VR-03
    Then the observed behavior matches the registered statement exactly

  @VR-04 @build
  Scenario: Every used external interface is elaborated in the unique reserved probe module.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_04 exercises VR-04
    Then the observed behavior matches the registered statement exactly

  @VR-05 @build
  Scenario: Generated modules compile in topological order and produce one required olean each.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_05 exercises VR-05
    Then the observed behavior matches the registered statement exactly

  @VR-06 @build
  Scenario: Verification neither requests nor includes ilean artifacts.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_06 exercises VR-06
    Then the observed behavior matches the registered statement exactly

  @VR-07 @build
  Scenario: A Lean warning, unknown informational message, overflow, or missing output fails verification.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_07 exercises VR-07
    Then the observed behavior matches the registered statement exactly

  @VR-08 @build
  Scenario: Every generated module is replayed by a separate leanchecker process and every replay must succeed.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_08 exercises VR-08
    Then the observed behavior matches the registered statement exactly

  @VR-09 @build
  Scenario: The unique reserved audit module prints axioms for every generated declaration exactly once.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_09 exercises VR-09
    Then the observed behavior matches the registered statement exactly

  @VR-10 @build
  Scenario: The axiom parser accepts only the pinned exact output forms and rejects missing, duplicate, extra, or malformed records.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_10 exercises VR-10
    Then the observed behavior matches the registered statement exactly

  @VR-11 @build
  Scenario: None, allow-subset, and exact axiom policies are enforced exactly and recorded per declaration.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_11 exercises VR-11
    Then the observed behavior matches the registered statement exactly

  @VR-12 @build
  Scenario: Child process output is normalized with the exact path and line rules before hashing.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_12 exercises VR-12
    Then the observed behavior matches the registered statement exactly

  @VR-13 @build
  Scenario: A verified directory contains the complete fixed source, map, coverage, olean, probe, audit, and process artifact set.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_13 exercises VR-13
    Then the observed behavior matches the registered statement exactly

  @VR-14 @build
  Scenario: The attestation ID is computed over the canonical body with its ID field removed.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_14 exercises VR-14
    Then the observed behavior matches the registered statement exactly

  @VR-15 @build
  Scenario: Any failed verification stage removes staging and produces no verified artifact or verified status.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_15 exercises VR-15
    Then the observed behavior matches the registered statement exactly

  @VR-16 @build
  Scenario: Axioms flowing from imported theorems remain subject to the generated declaration's policy.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_16 exercises VR-16
    Then the observed behavior matches the registered statement exactly

  @VR-17 @build
  Scenario: Lean workspace configuration and manifest hashes must match the lock and all dependencies must be locally available.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_17 exercises VR-17
    Then the observed behavior matches the registered statement exactly

  @VR-18 @build
  Scenario: Check and build results never claim verified or kernel-checked status.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_vr_18 exercises VR-18
    Then the observed behavior matches the registered statement exactly
