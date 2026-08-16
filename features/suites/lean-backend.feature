Feature: lean-backend

  Prose-free deterministic Lean generation (§18).

  @LN-01 @build
  Scenario: Each generated Lean file has the exact module, import, option, namespace, declaration, and end structure.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_01 exercises LN-01
    Then the observed behavior matches the registered statement exactly

  @LN-02 @build
  Scenario: Imports are explicit, deduplicated, sorted, and every external global is fully qualified.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_02 exercises LN-02
    Then the observed behavior matches the registered statement exactly

  @LN-03 @build
  Scenario: Generated Lean contains no comments, documentation, strings, or copied source prose.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_03 exercises LN-03
    Then the observed behavior matches the registered statement exactly

  @LN-04 @build
  Scenario: Generated Lean contains no sorry, admit, axiom, opaque, unsafe, native_decide, or placeholder declaration.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_04 exercises LN-04
    Then the observed behavior matches the registered statement exactly

  @LN-05 @build
  Scenario: Every linked term and proof variant has one defined Lean lowering and missing lowering is a hard error.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_05 exercises LN-05
    Then the observed behavior matches the registered statement exactly

  @LN-06 @build
  Scenario: Leading universal binders become deterministic declaration parameters with complete source mapping.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_06 exercises LN-06
    Then the observed behavior matches the registered statement exactly

  @LN-07 @build
  Scenario: All document definitions emit def and never alternate declaration forms.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_07 exercises LN-07
    Then the observed behavior matches the registered statement exactly

  @LN-08 @build
  Scenario: Proof lowering uses only the fixed pinned Lean forms enumerated by the specification.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_08 exercises LN-08
    Then the observed behavior matches the registered statement exactly

  @LN-09 @build
  Scenario: Lean formatting is byte-deterministic with fixed indentation, LF, and final LF.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_09 exercises LN-09
    Then the observed behavior matches the registered statement exactly

  @LN-10 @build
  Scenario: Every non-whitespace generated Lean token has a source, glossary, IR, or synthetic-core mapping.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_10 exercises LN-10
    Then the observed behavior matches the registered statement exactly

  @LN-11 @build
  Scenario: The generated-source audit tokenizes and rejects prose-bearing or forbidden Lean tokens before verification.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_11 exercises LN-11
    Then the observed behavior matches the registered statement exactly

  @LN-12 @build
  Scenario: Generated file paths and module names exactly mirror the configured module prefix and source module.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ln_12 exercises LN-12
    Then the observed behavior matches the registered statement exactly
