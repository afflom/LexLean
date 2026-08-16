Feature: security

  Filesystem confinement, process policy, limits, and internal invariants (§25).

  @SE-01 @build
  Scenario: Source, package, workspace, resource, and output paths are confined and symlinks are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_01 exercises SE-01
    Then the observed behavior matches the registered statement exactly

  @SE-02 @build
  Scenario: Special files, duplicate filesystem identities, and case-fold collisions are rejected before processing.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_02 exercises SE-02
    Then the observed behavior matches the registered statement exactly

  @SE-03 @build
  Scenario: All child processes use direct executable and argv invocation with no shell.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_03 exercises SE-03
    Then the observed behavior matches the registered statement exactly

  @SE-04 @build
  Scenario: No command except lock --allow-network may perform package network acquisition.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_04 exercises SE-04
    Then the observed behavior matches the registered statement exactly

  @SE-05 @build
  Scenario: Child environments use the specified deterministic allow-list and recorded normalization.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_05 exercises SE-05
    Then the observed behavior matches the registered statement exactly

  @SE-06 @build
  Scenario: Every configured parser, graph, IR, diagnostic, child-output, and timeout limit is enforced with checked arithmetic.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_06 exercises SE-06
    Then the observed behavior matches the registered statement exactly

  @SE-07 @build
  Scenario: Temporary data uses confined owner-only staging and is removed after atomic publication or failure.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_07 exercises SE-07
    Then the observed behavior matches the registered statement exactly

  @SE-08 @build
  Scenario: External executables and PDF resources are hash-checked before use.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_08 exercises SE-08
    Then the observed behavior matches the registered statement exactly

  @SE-09 @build
  Scenario: PDF execution receives only canonical TeX and declared resources in an isolated working directory.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_09 exercises SE-09
    Then the observed behavior matches the registered statement exactly

  @SE-10 @build
  Scenario: Internal invariant failures use LLI9001 and exit 70 without misclassifying user input.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_10 exercises SE-10
    Then the observed behavior matches the registered statement exactly

  @SE-11 @build
  Scenario: Diagnostics and process records do not expose secret environment values or arbitrary unrelated file contents.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_11 exercises SE-11
    Then the observed behavior matches the registered statement exactly

  @SE-12 @build
  Scenario: Git lexicon acquisition accepts only an exact 40-hex commit over HTTPS and rejects submodules and LFS indirection.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_se_12 exercises SE-12
    Then the observed behavior matches the registered statement exactly
