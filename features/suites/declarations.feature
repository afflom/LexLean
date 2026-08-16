Feature: declarations

  Definition sentences, theorem-like components, and axiom policies (§15.7-§15.9, §18.6).

  @DF-01 @build
  Scenario: A valid type-definition sentence emits one nonrecursive sort-valued Lean def linked to its document entry.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_01 exercises DF-01
    Then the observed behavior matches the registered statement exactly

  @DF-02 @build
  Scenario: A valid term-definition sentence emits one nonrecursive explicitly typed Lean def.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_02 exercises DF-02
    Then the observed behavior matches the registered statement exactly

  @DF-03 @build
  Scenario: A valid predicate-definition sentence emits one nonrecursive Prop-valued Lean def.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_03 exercises DF-03
    Then the observed behavior matches the registered statement exactly

  @DF-04 @build
  Scenario: Self recursion, mutual recursion, and later-declaration references are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_04 exercises DF-04
    Then the observed behavior matches the registered statement exactly

  @DF-05 @build
  Scenario: A definition's self head, explicit arguments, and signature order are checked exactly.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_05 exercises DF-05
    Then the observed behavior matches the registered statement exactly

  @DF-06 @build
  Scenario: Every generated definition and theorem-like declaration carries one explicit axiom policy.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_06 exercises DF-06
    Then the observed behavior matches the registered statement exactly

  @DF-07 @build
  Scenario: Theorem, lemma, and corollary each emit Lean theorem declarations while retaining distinct document metadata.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_07 exercises DF-07
    Then the observed behavior matches the registered statement exactly

  @DF-08 @build
  Scenario: Author-defined axioms, opaque declarations, and proofless theorem-like components are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_08 exercises DF-08
    Then the observed behavior matches the registered statement exactly

  @DF-09 @build
  Scenario: Every theorem-like component contains exactly one nonempty structured proof.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_09 exercises DF-09
    Then the observed behavior matches the registered statement exactly

  @DF-10 @build
  Scenario: Generated declarations preserve source order and every document reference respects that order.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_df_10 exercises DF-10
    Then the observed behavior matches the registered statement exactly
