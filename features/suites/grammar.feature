Feature: grammar

  The structural, phrase, mathematical-island, and proposition grammars (§15).

  @GR-01 @build
  Scenario: A source module parses only under the exact structural grammar and environment set.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_01 exercises GR-01
    Then the observed behavior matches the registered statement exactly

  @GR-02 @build
  Scenario: Glossary imports, module imports, title, and blocks obey exact header order and cardinality.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_02 exercises GR-02
    Then the observed behavior matches the registered statement exactly

  @GR-03 @build
  Scenario: Sections nest within the configured scope limit and section parameters introduce explicit inherited context.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_03 exercises GR-03
    Then the observed behavior matches the registered statement exactly

  @GR-04 @build
  Scenario: Titles and headings accept only bounded concept phrases and cannot encode an unproved proposition.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_04 exercises GR-04
    Then the observed behavior matches the registered statement exactly

  @GR-05 @build
  Scenario: Only parenthesized and display control delimiters create math islands; dollar math is rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_05 exercises GR-05
    Then the observed behavior matches the registered statement exactly

  @GR-06 @build
  Scenario: Dynamic mathematical operators obey declared precedence, associativity, and explicit grouping.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_06 exercises GR-06
    Then the observed behavior matches the registered statement exactly

  @GR-07 @build
  Scenario: Mathematical juxtaposition is never interpreted as implicit multiplication or application.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_07 exercises GR-07
    Then the observed behavior matches the registered statement exactly

  @GR-08 @build
  Scenario: Universal, existential, unique-existential, conditional, and connective proposition forms have the specified compositional semantics.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_08 exercises GR-08
    Then the observed behavior matches the registered statement exactly

  @GR-09 @build
  Scenario: Proposition precedence and associativity produce the specified parse or an ambiguity error.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_09 exercises GR-09
    Then the observed behavior matches the registered statement exactly

  @GR-10 @build
  Scenario: Articles, plural forms, capitalization, and inflections are explicit lexicon data rather than inferred language rules.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_10 exercises GR-10
    Then the observed behavior matches the registered statement exactly

  @GR-11 @build
  Scenario: A component with no complete grammar parse fails with a bounded structured diagnostic.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_11 exercises GR-11
    Then the observed behavior matches the registered statement exactly

  @GR-12 @build
  Scenario: Distinct surviving parses fail as ambiguity while semantically identical canonical IR alternatives collapse.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_12 exercises GR-12
    Then the observed behavior matches the registered statement exactly

  @GR-13 @build
  Scenario: Free expository paragraphs and opaque text nodes are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_13 exercises GR-13
    Then the observed behavior matches the registered statement exactly

  @GR-14 @build
  Scenario: Definition and theorem-like components enforce exact sentence, policy, and proof cardinalities.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_14 exercises GR-14
    Then the observed behavior matches the registered statement exactly

  @GR-15 @build
  Scenario: Explicit module imports form an acyclic graph and selected builds include their transitive closure.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_15 exercises GR-15
    Then the observed behavior matches the registered statement exactly

  @GR-16 @build
  Scenario: A same-module declaration cannot reference a later declaration.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gr_16 exercises GR-16
    Then the observed behavior matches the registered statement exactly
