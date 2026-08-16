Feature: latex-pdf

  Canonical LaTeX rendering, output coverage, and the external PDF protocol (§19).

  @TX-01 @build
  Scenario: Canonical LaTeX is rendered solely from linked IR and never copies source text or controls.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_01 exercises TX-01
    Then the observed behavior matches the registered statement exactly

  @TX-02 @build
  Scenario: Every module uses the exact canonical LaTeX preamble and no host or timestamp metadata.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_02 exercises TX-02
    Then the observed behavior matches the registered statement exactly

  @TX-03 @build
  Scenario: Statements use only canonical controlled proposition and definition renderings.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_03 exercises TX-03
    Then the observed behavior matches the registered statement exactly

  @TX-04 @build
  Scenario: Proof prose is generated from proof IR using fixed core lexical forms.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_04 exercises TX-04
    Then the observed behavior matches the registered statement exactly

  @TX-05 @build
  Scenario: Titles, sections, parameters, environments, numbering, and labels follow the exact document rules.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_05 exercises TX-05
    Then the observed behavior matches the registered statement exactly

  @TX-06 @build
  Scenario: Every visible LaTeX word, symbol, punctuation mark, and control has complete coverage.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_06 exercises TX-06
    Then the observed behavior matches the registered statement exactly

  @TX-07 @build
  Scenario: Non-core lexicons cannot inject a raw TeX control or unclassified output segment.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_07 exercises TX-07
    Then the observed behavior matches the registered statement exactly

  @TX-08 @build
  Scenario: Canonical LaTeX bytes are deterministic, LF-normalized, and final-LF terminated.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_08 exercises TX-08
    Then the observed behavior matches the registered statement exactly

  @TX-09 @build
  Scenario: An enabled external PDF provider runs without a shell in an isolated directory with exact hashes and resources.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_09 exercises TX-09
    Then the observed behavior matches the registered statement exactly

  @TX-10 @build
  Scenario: The PDF recipe ID and actual PDF hash use the specified independent content records.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_10 exercises TX-10
    Then the observed behavior matches the registered statement exactly

  @TX-11 @build
  Scenario: PDF success or failure never changes mathematical verification authority.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_11 exercises TX-11
    Then the observed behavior matches the registered statement exactly

  @TX-12 @build
  Scenario: The publishable document is the canonical renderer output rather than unchecked source bytes.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_tx_12 exercises TX-12
    Then the observed behavior matches the registered statement exactly
