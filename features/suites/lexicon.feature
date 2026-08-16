Feature: lexicon

  Lexicon packages, entries, forms, denotations, LSE, LRE, and renderer tokens (§13, §16.11).

  @GL-01 @build
  Scenario: Lexicon packages obey the exact package layout, schema, ID-to-path rule, and exact imports.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_01 exercises GL-01
    Then the observed behavior matches the registered statement exactly

  @GL-02 @build
  Scenario: Entry files obey the exact entry schema and category-specific field rules.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_02 exercises GL-02
    Then the observed behavior matches the registered statement exactly

  @GL-03 @build
  Scenario: Forms obey channel, feature, canonical-source, safety, and explicit-inflection requirements.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_03 exercises GL-03
    Then the observed behavior matches the registered statement exactly

  @GL-04 @build
  Scenario: Every entry uses one fixed frame and packages cannot add grammar productions.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_04 exercises GL-04
    Then the observed behavior matches the registered statement exactly

  @GL-05 @build
  Scenario: Denotations are exactly core, Lean, document, or acyclic defined values.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_05 exercises GL-05
    Then the observed behavior matches the registered statement exactly

  @GL-06 @build
  Scenario: Every semantic entry has a valid canonical LSE signature with scoped binders and universes.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_06 exercises GL-06
    Then the observed behavior matches the registered statement exactly

  @GL-07 @build
  Scenario: Every canonical render uses valid LRE with complete slot use and no raw TeX.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_07 exercises GL-07
    Then the observed behavior matches the registered statement exactly

  @GL-08 @build
  Scenario: Only the core renderer-token registry can authorize emitted LaTeX controls and glyphs.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_08 exercises GL-08
    Then the observed behavior matches the registered statement exactly

  @GL-09 @build
  Scenario: Package import cycles and excessive import depth are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_09 exercises GL-09
    Then the observed behavior matches the registered statement exactly

  @GL-10 @build
  Scenario: Defined-denotation cycles and document-definition cycles are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_10 exercises GL-10
    Then the observed behavior matches the registered statement exactly

  @GL-11 @build
  Scenario: A document denotation must resolve to an available declaration with a matching signature.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_11 exercises GL-11
    Then the observed behavior matches the registered statement exactly

  @GL-12 @build
  Scenario: Every used external Lean entry is checked by a generated interface probe during verification.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_12 exercises GL-12
    Then the observed behavior matches the registered statement exactly

  @GL-13 @build
  Scenario: Duplicate packages, entries, forms, and qualified IDs are rejected while same-surface overloads remain explicit candidates.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_13 exercises GL-13
    Then the observed behavior matches the registered statement exactly

  @GL-14 @build
  Scenario: Cases and induction are available only through a complete validated eliminator descriptor.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_14 exercises GL-14
    Then the observed behavior matches the registered statement exactly

  @GL-15 @build
  Scenario: Glossary files reject free description, documentation, note, meaning, and unknown prose fields.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_15 exercises GL-15
    Then the observed behavior matches the registered statement exactly

  @GL-16 @build
  Scenario: Package and entry bytes participate in lock and semantic closure hashes exactly as specified.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_gl_16 exercises GL-16
    Then the observed behavior matches the registered statement exactly
