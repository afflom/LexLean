Feature: semantic-ir

  Compiler phases, closed IR variants, conservative elaboration, and content identity (§17, §21).

  @SM-01 @build
  Scenario: Compiler phases execute in the required order and no backend receives an unlinked or ambiguous program.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_01 exercises SM-01
    Then the observed behavior matches the registered statement exactly

  @SM-02 @build
  Scenario: Every global and local reference has one closed typed reference variant and one stable identity.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_02 exercises SM-02
    Then the observed behavior matches the registered statement exactly

  @SM-03 @build
  Scenario: Term IR contains only the specified closed variants and represents every accepted semantic term.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_03 exercises SM-03
    Then the observed behavior matches the registered statement exactly

  @SM-04 @build
  Scenario: Proof IR contains only the specified closed variants and represents every accepted proof form.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_04 exercises SM-04
    Then the observed behavior matches the registered statement exactly

  @SM-05 @build
  Scenario: Conservative signature elaboration checks arity, binders, categories, and expected types without claiming Lean kernel equivalence.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_05 exercises SM-05
    Then the observed behavior matches the registered statement exactly

  @SM-06 @build
  Scenario: Omitted implicit binders are recorded as controlled application metadata and user holes are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_06 exercises SM-06
    Then the observed behavior matches the registered statement exactly

  @SM-07 @build
  Scenario: Document-entry signatures and generated declaration signatures are compared canonically before rendering.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_07 exercises SM-07
    Then the observed behavior matches the registered statement exactly

  @SM-08 @build
  Scenario: Module, component, local, and hypothesis name generation is deterministic and collision checked.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_08 exercises SM-08
    Then the observed behavior matches the registered statement exactly

  @SM-09 @build
  Scenario: Linked IR has stable schema-tagged canonical JSON with alpha-safe binder serialization.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_09 exercises SM-09
    Then the observed behavior matches the registered statement exactly

  @SM-10 @build
  Scenario: Source ID and semantic ID use exactly the specified framed hash inputs.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_10 exercises SM-10
    Then the observed behavior matches the registered statement exactly

  @SM-11 @build
  Scenario: Linked project result sets contain every selected module and imported module exactly once in stable order.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_11 exercises SM-11
    Then the observed behavior matches the registered statement exactly

  @SM-12 @build
  Scenario: No semantic IR node can contain opaque prose, raw backend text, or an unknown extension.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_12 exercises SM-12
    Then the observed behavior matches the registered statement exactly

  @SM-13 @build
  Scenario: Inherited section parameters are represented explicitly and emitted only on declarations that use them.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_13 exercises SM-13
    Then the observed behavior matches the registered statement exactly

  @SM-14 @build
  Scenario: A numeral without a unique expected type is rejected rather than defaulted.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_sm_14 exercises SM-14
    Then the observed behavior matches the registered statement exactly
