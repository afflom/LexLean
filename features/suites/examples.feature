Feature: examples

  The literal example, its required mutations, and the negative fixture suite (§28, §29).

  @EX-01 @build
  Scenario: The committed nat-add-zero example formats, locks, checks, builds, and verifies with an empty axiom set.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ex_01 exercises EX-01
    Then the observed behavior matches the registered statement exactly

  @EX-02 @build
  Scenario: Changing the example proposition while retaining the old proof causes remapped Lean verification failure.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ex_02 exercises EX-02
    Then the observed behavior matches the registered statement exactly

  @EX-03 @build
  Scenario: Replacing a title concept with an undeclared word causes lexical-closure failure.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ex_03 exercises EX-03
    Then the observed behavior matches the registered statement exactly

  @EX-04 @build
  Scenario: Adding an indistinguishable same-surface entry causes ambiguity rather than priority selection.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ex_04 exercises EX-04
    Then the observed behavior matches the registered statement exactly

  @EX-05 @build
  Scenario: An axiom-dependent fixture fails an insufficient declaration policy and records the observed excess.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ex_05 exercises EX-05
    Then the observed behavior matches the registered statement exactly

  @EX-06 @build
  Scenario: Two clean example builds in distinct paths have byte-identical platform-independent artifacts.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ex_06 exercises EX-06
    Then the observed behavior matches the registered statement exactly

  @EX-07 @build
  Scenario: The negative fixture suite covers every required rejection class and prescribed diagnostic family.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ex_07 exercises EX-07
    Then the observed behavior matches the registered statement exactly

  @EX-08 @build
  Scenario: Every example directory is discovered automatically and must satisfy the full example gate.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_ex_08 exercises EX-08
    Then the observed behavior matches the registered statement exactly
