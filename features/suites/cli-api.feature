Feature: cli-api

  The command-line interface and the stable public Rust API (§23, §24).

  @CL-01 @build
  Scenario: Global options and upward project discovery obey the exact CLI contract.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_01 exercises CL-01
    Then the observed behavior matches the registered statement exactly

  @CL-02 @build
  Scenario: Init creates the complete canonical skeleton only in an absent or empty destination and never overwrites.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_02 exercises CL-02
    Then the observed behavior matches the registered statement exactly

  @CL-03 @build
  Scenario: Lock check, local update, and explicit network acquisition obey their exact mutually exclusive behavior.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_03 exercises CL-03
    Then the observed behavior matches the registered statement exactly

  @CL-04 @build
  Scenario: Check runs through linked IR and emits no build artifacts.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_04 exercises CL-04
    Then the observed behavior matches the registered statement exactly

  @CL-05 @build
  Scenario: Build emits the fixed build-ID artifact set without running Lean or claiming verification.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_05 exercises CL-05
    Then the observed behavior matches the registered statement exactly

  @CL-06 @build
  Scenario: Verify runs the complete fixed verification pipeline and accepts no output or suppression option.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_06 exercises CL-06
    Then the observed behavior matches the registered statement exactly

  @CL-07 @build
  Scenario: Format and format-check are idempotent and preserve linked IR.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_07 exercises CL-07
    Then the observed behavior matches the registered statement exactly

  @CL-08 @build
  Scenario: Clean removes only the validated configured build root and no source or external cache.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_08 exercises CL-08
    Then the observed behavior matches the registered statement exactly

  @CL-09 @build
  Scenario: Explain prints exactly one registered diagnostic entry and rejects unknown codes.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_09 exercises CL-09
    Then the observed behavior matches the registered statement exactly

  @CL-10 @build
  Scenario: All, explicit-files, and entrypoint selections return sorted project result sets including import closure.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_10 exercises CL-10
    Then the observed behavior matches the registered statement exactly

  @CL-11 @build
  Scenario: Every command maps failures to the exact documented exit code.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_11 exercises CL-11
    Then the observed behavior matches the registered statement exactly

  @CL-12 @build
  Scenario: Human and canonical-JSON output modes obey exact stream, color, and cardinality rules.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_12 exercises CL-12
    Then the observed behavior matches the registered statement exactly

  @CL-13 @build
  Scenario: The public Engine exposes exactly the stable load, lock, check, build, verify, and format entry points.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_13 exercises CL-13
    Then the observed behavior matches the registered statement exactly

  @CL-14 @build
  Scenario: Every public multi-module operation returns a ProjectResultSet or VerifiedProject rather than a singular unit.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_14 exercises CL-14
    Then the observed behavior matches the registered statement exactly

  @CL-15 @build
  Scenario: Public requests cannot override backends, toolchain, verification stages, limits, policies, or fixed artifact sets.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_15 exercises CL-15
    Then the observed behavior matches the registered statement exactly

  @CL-16 @build
  Scenario: Every public failure is a LexLeanError and malformed user input cannot panic.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_16 exercises CL-16
    Then the observed behavior matches the registered statement exactly

  @CL-17 @build
  Scenario: Environment variables cannot alter semantic project configuration.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_17 exercises CL-17
    Then the observed behavior matches the registered statement exactly

  @CL-18 @build
  Scenario: Version output reports compiler, language, semantics ID, and Lean toolchain exactly.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cl_18 exercises CL-18
    Then the observed behavior matches the registered statement exactly
