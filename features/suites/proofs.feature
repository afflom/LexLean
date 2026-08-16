Feature: proofs

  The structured proof language and its conservative checking (§16).

  @PF-01 @build
  Scenario: Assume and exact-style simple proof sentences create scoped introductions and exact proof nodes.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_01 exercises PF-01
    Then the observed behavior matches the registered statement exactly

  @PF-02 @build
  Scenario: Simple Apply is accepted only when its declared signature yields exactly one residual premise.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_02 exercises PF-02
    Then the observed behavior matches the registered statement exactly

  @PF-03 @build
  Scenario: Structured apply requires every numbered residual premise exactly once and in signature order.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_03 exercises PF-03
    Then the observed behavior matches the registered statement exactly

  @PF-04 @build
  Scenario: Reflexivity lowers only to pinned Lean rfl and closes the current goal.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_04 exercises PF-04
    Then the observed behavior matches the registered statement exactly

  @PF-05 @build
  Scenario: Witness steps supply the next existential witness with no implicit search.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_05 exercises PF-05
    Then the observed behavior matches the registered statement exactly

  @PF-06 @build
  Scenario: Left and right alternative steps select only the corresponding disjunction constructor.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_06 exercises PF-06
    Then the observed behavior matches the registered statement exactly

  @PF-07 @build
  Scenario: Have establishes a nested proposition before introducing its fresh hypothesis into subsequent scope.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_07 exercises PF-07
    Then the observed behavior matches the registered statement exactly

  @PF-08 @build
  Scenario: Rewrite applies every explicitly directed rule strictly in source order at exactly one target.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_08 exercises PF-08
    Then the observed behavior matches the registered statement exactly

  @PF-09 @build
  Scenario: Simplify lowers to simp only with exactly the listed rules and target.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_09 exercises PF-09
    Then the observed behavior matches the registered statement exactly

  @PF-10 @build
  Scenario: Constructor requires the exact ordered branch count and every branch closes.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_10 exercises PF-10
    Then the observed behavior matches the registered statement exactly

  @PF-11 @build
  Scenario: Cases requires a validated descriptor, every constructor once, and exact branch binders.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_11 exercises PF-11
    Then the observed behavior matches the registered statement exactly

  @PF-12 @build
  Scenario: Induction requires a validated descriptor, every constructor once, and exact field and induction-hypothesis binders.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_12 exercises PF-12
    Then the observed behavior matches the registered statement exactly

  @PF-13 @build
  Scenario: Calculation chains use one declared relation, at least one step, and exact endpoint proofs.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_13 exercises PF-13
    Then the observed behavior matches the registered statement exactly

  @PF-14 @build
  Scenario: Proof locals, hypotheses, premise scopes, and case scopes cannot capture or leak.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_14 exercises PF-14
    Then the observed behavior matches the registered statement exactly

  @PF-15 @build
  Scenario: Every proof and nested branch must close all goals and rejects steps after closure.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_15 exercises PF-15
    Then the observed behavior matches the registered statement exactly

  @PF-16 @build
  Scenario: Raw tactics, custom proof nodes, unrestricted automation, and proof holes are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_16 exercises PF-16
    Then the observed behavior matches the registered statement exactly

  @PF-17 @build
  Scenario: native_decide is never accepted or generated.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_17 exercises PF-17
    Then the observed behavior matches the registered statement exactly

  @PF-18 @build
  Scenario: Lean proof failures remap to the smallest originating LexLean proof or statement span.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_pf_18 exercises PF-18
    Then the observed behavior matches the registered statement exactly
