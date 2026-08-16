Feature: artifacts

  Diagnostics, source maps, coverage, hashing, manifests, and atomic publication (§20, §21).

  @AR-01 @build
  Scenario: Diagnostics use the canonical schema, exact spans, stable sorting, and registered codes.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_01 exercises AR-01
    Then the observed behavior matches the registered statement exactly

  @AR-02 @build
  Scenario: Source maps contain complete module, source, artifact, node, and range records.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_02 exercises AR-02
    Then the observed behavior matches the registered statement exactly

  @AR-03 @build
  Scenario: Lean diagnostics remap by the specified smallest-enclosing mapping algorithm.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_03 exercises AR-03
    Then the observed behavior matches the registered statement exactly

  @AR-04 @build
  Scenario: Coverage files record every required source and output token with no gap or overlap.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_04 exercises AR-04
    Then the observed behavior matches the registered statement exactly

  @AR-05 @build
  Scenario: All compound hashes use the specified length-prefixed frame function.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_05 exercises AR-05
    Then the observed behavior matches the registered statement exactly

  @AR-06 @build
  Scenario: Compiler-semantics identity is recomputed from the exact normative language, schema, backend, and parser inputs.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_06 exercises AR-06
    Then the observed behavior matches the registered statement exactly

  @AR-07 @build
  Scenario: Source IDs are independent of absolute checkout location and include exact normalized inputs.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_07 exercises AR-07
    Then the observed behavior matches the registered statement exactly

  @AR-08 @build
  Scenario: Semantic IDs are platform independent and include linked IR, lexicon closure, language semantics, and toolchain ID.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_08 exercises AR-08
    Then the observed behavior matches the registered statement exactly

  @AR-09 @build
  Scenario: Successful builds publish only the fixed content-addressed build-ID layout.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_09 exercises AR-09
    Then the observed behavior matches the registered statement exactly

  @AR-10 @build
  Scenario: Build manifests enumerate every input and output with stable paths, sizes, and hashes.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_10 exercises AR-10
    Then the observed behavior matches the registered statement exactly

  @AR-11 @build
  Scenario: Normative JSON obeys the restricted canonical JSON format and hash/file newline distinction.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_11 exercises AR-11
    Then the observed behavior matches the registered statement exactly

  @AR-12 @build
  Scenario: Concurrent and failed builds preserve atomic content-addressed artifacts and never overwrite unexplained bytes.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_12 exercises AR-12
    Then the observed behavior matches the registered statement exactly

  @AR-13 @build
  Scenario: Two clean builds in different absolute directories produce byte-identical platform-independent artifacts.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_13 exercises AR-13
    Then the observed behavior matches the registered statement exactly

  @AR-14 @build
  Scenario: Platform-independent build evidence is distinguished from platform-bound oleans, process records, PDF bytes, and attestations.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ar_14 exercises AR-14
    Then the observed behavior matches the registered statement exactly
