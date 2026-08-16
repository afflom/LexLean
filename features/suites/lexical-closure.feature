Feature: lexical-closure

  Source normalization, the primitive scanner, and closed lexical resolution (§12, §14).

  @LX-01 @build
  Scenario: Source decoding and line normalization enforce valid UTF-8, LF, final LF, and forbidden-scalar rules.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_01 exercises LX-01
    Then the observed behavior matches the registered statement exactly

  @LX-02 @build
  Scenario: Non-NFC source is diagnosed and canonical formatting rewrites it without semantic change.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_02 exercises LX-02
    Then the observed behavior matches the registered statement exactly

  @LX-03 @build
  Scenario: Raw percent, comments, tabs, trailing spaces, and non-ASCII whitespace are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_03 exercises LX-03
    Then the observed behavior matches the registered statement exactly

  @LX-04 @build
  Scenario: The primitive scanner recognizes exactly the specified atom classes and records exact spans.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_04 exercises LX-04
    Then the observed behavior matches the registered statement exactly

  @LX-05 @build
  Scenario: Core braces, controls, punctuation, and grammar tokens receive glossary coverage rather than TeX trust.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_05 exercises LX-05
    Then the observed behavior matches the registered statement exactly

  @LX-06 @build
  Scenario: An undeclared prose word is rejected with an exact unknown-atom diagnostic.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_06 exercises LX-06
    Then the observed behavior matches the registered statement exactly

  @LX-07 @build
  Scenario: An undeclared symbol or control sequence is rejected with an exact unknown-atom diagnostic.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_07 exercises LX-07
    Then the observed behavior matches the registered statement exactly

  @LX-08 @build
  Scenario: Lexical analysis builds all valid form edges without greedy import-order selection.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_08 exercises LX-08
    Then the observed behavior matches the registered statement exactly

  @LX-09 @build
  Scenario: Every accepted non-whitespace source atom is covered exactly once in the selected path.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_09 exercises LX-09
    Then the observed behavior matches the registered statement exactly

  @LX-10 @build
  Scenario: A local identifier is accepted only when introduced by a binder and every later occurrence resolves by scope.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_10 exercises LX-10
    Then the observed behavior matches the registered statement exactly

  @LX-11 @build
  Scenario: TeX macro definition, expansion, file access, and execution controls are rejected even if a package declares them.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_11 exercises LX-11
    Then the observed behavior matches the registered statement exactly

  @LX-12 @build
  Scenario: Qualified lexeme and document-reference controls select only existing closed entries or declarations.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_12 exercises LX-12
    Then the observed behavior matches the registered statement exactly

  @LX-13 @build
  Scenario: Lexical or semantic ambiguity is rejected and no priority or heuristic chooses a candidate.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_13 exercises LX-13
    Then the observed behavior matches the registered statement exactly

  @LX-14 @build
  Scenario: Canonical formatting chooses safe canonical forms and proves linked-IR preservation.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_lx_14 exercises LX-14
    Then the observed behavior matches the registered statement exactly
