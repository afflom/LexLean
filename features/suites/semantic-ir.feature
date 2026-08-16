Feature: semantic-ir

  Compiler phases, closed IR variants, conservative elaboration, and content identity (§17, §21).

  @SM-01 @build
  Scenario: Compiler phases execute in the required order and no backend receives an unlinked or ambiguous program.
    Given the example project with a tab and the unknown word `banana` both inserted into the theorem statement
    When lexlean check runs
    Then the first diagnostic is the normalization error LLL1002 rather than a lexical error
    And building a project with only `banana` inserted fails without creating `.lexlean/build`

  @SM-02 @build
  Scenario: Every global and local reference has one closed typed reference variant and one stable identity.
    Given the `test.defs` project with a type, term, and predicate definition plus the `add-zero` theorem
    When the linked IR is serialized to canonical JSON and every `kind` tag is collected
    Then the tags are drawn only from `core`, `external`, `document`, `defined`, the definition and theorem kinds, and the policy kinds
    And a second check of the same project reproduces the same semantic ID and identical canonical JSON bytes

  @SM-03 @build
  Scenario: Term IR contains only the specified closed variants and represents every accepted semantic term.
    Given the example project and the `test.defs` project
    When each linked IR is serialized to canonical JSON and every `k` tag is collected
    Then no term tag falls outside `sort`, `local`, `global`, `app`, `pi`, `lam`, `let`, and `nat`
    And the corpus exercises `app`, `pi`, and `global`

  @SM-04 @build
  Scenario: Proof IR contains only the specified closed variants and represents every accepted proof form.
    Given the example project and the `test.defs` project whose proofs close goals by reflexivity
    When each linked IR is serialized to canonical JSON and every proof `k` tag is collected
    Then no proof tag falls outside the closed set from `seq` and `intro` through `induction` and `calc`
    And the corpus exercises the `rfl` proof variant

  @SM-05 @build
  Scenario: Conservative signature elaboration checks arity, binders, categories, and expected types without claiming Lean kernel equivalence.
    Given the example project with the statement `\(n + 0 = n\) and \(n + 0\)` whose second conjunct is a term, not a proposition
    When lexlean check runs
    Then it fails with LLT4001 or LLP2001 from conservative elaboration
    And no Lean kernel is consulted to reach that verdict

  @SM-06 @build
  Scenario: Omitted implicit binders are recorded as controlled application metadata and user holes are rejected.
    Given the example project whose statement applies `Eq` with an omitted implicit type argument
    When the linked IR is serialized to canonical JSON
    Then the application carries an `"i":[` implicit-binder record
    And the statement rewritten as `\(n + _ = n\)` fails check with LLL1004 for the user hole

  @SM-07 @build
  Scenario: Document-entry signatures and generated declaration signatures are compared canonically before rendering.
    Given the `test.defs` project with the binder in `entries/double.toml` renamed from `n` to `renamed`
    When the project is relocked and lexlean check runs
    Then the alpha-renamed entry signature still matches the generated `double` declaration and the check succeeds

  @SM-08 @build
  Scenario: Module, component, local, and hypothesis name generation is deterministic and collision checked.
    Given the example project rendered twice
    When the Lean text for `Main` from both renders is compared
    Then the generated names are byte-identical
    And a copy with a second theorem also named `add-zero` fails check with LLP2003 or LLR3002 for the collision

  @SM-09 @build
  Scenario: Linked IR has stable schema-tagged canonical JSON with alpha-safe binder serialization.
    Given the example project and a copy with the bound variable `n` renamed to `m` throughout the statement
    When both projects are checked and the canonical key of the `add-zero` statement is computed
    Then the two alpha-renamed statements share one canonical key

  @SM-10 @build
  Scenario: Source ID and semantic ID use exactly the specified framed hash inputs.
    Given the example project checked through the internal pipeline
    When SHA-256 over `lexlean-source-v1\0` and the length-framed `project`, `lock`, `path`, and `source` inputs is recomputed by hand
    Then it equals the reported source ID
    And the semantic ID equals `semantic_id` of the compiler semantics ID, the canonical linked IR, and the closure JSON

  @SM-11 @build
  Scenario: Linked project result sets contain every selected module and imported module exactly once in stable order.
    Given the example project with a `Helper` copy of `Main` and `\importmodule{Helper}` added to `Main`
    When lexlean check runs with the entrypoint selection
    Then the result units are exactly `Helper` then `Main` in sorted order
    And the `All` selection returns the same complete sorted set

  @SM-12 @build
  Scenario: No semantic IR node can contain opaque prose, raw backend text, or an unknown extension.
    Given the example project checked through the internal pipeline
    When the linked IR is serialized to canonical JSON
    Then the JSON contains none of `natural number`, `For every`, `reflexivity`, or `Close the goal`

  @SM-13 @build
  Scenario: Inherited section parameters are represented explicitly and emitted only on declarations that use them.
    Given a `Main` module whose `basics` section has `\parameters{natural number \(p\)}` and theorems `uses-param` and `ignores-param`
    When the project is checked and each declaration's parameter list is inspected
    Then `uses-param` inherits exactly one binder
    And `ignores-param` inherits none

  @SM-14 @build
  Scenario: A numeral without a unique expected type is rejected rather than defaulted.
    Given the example project with the theorem statement `\(1 = 1\)`
    When lexlean check runs
    Then it fails with LLT4001 or LLP2002 because the numeral has no unique expected type
    And no default type is chosen for `1`
