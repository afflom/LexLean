Feature: lean-backend

  Prose-free deterministic Lean generation (§18).

  @LN-01 @build
  Scenario: Each generated Lean file has the exact module, import, option, namespace, declaration, and end structure.
    Given the nat-add-zero example project rendered without Lean or publication
    When the generated `Main` Lean text is scanned in order
    Then `module` opens the file as its first line
    And `import Init`, `set_option autoImplicit false`, `namespace LexLeanExample.Main`, `theorem add_zero`, and `end LexLeanExample.Main` occur in that order

  @LN-02 @build
  Scenario: Imports are explicit, deduplicated, sorted, and every external global is fully qualified.
    Given the nat-add-zero example project rendered to Lean
    When the `import` lines of the generated `Main` module are collected
    Then the import list equals its sorted and deduplicated form
    And the external global appears fully qualified as `Nat.add`
    And no `open` statement occurs anywhere in the file

  @LN-03 @build
  Scenario: Generated Lean contains no comments, documentation, strings, or copied source prose.
    Given the generated Lean for the nat-add-zero example and for the test.defs definitions fixture
    When each Lean text is searched for comment and string markers
    Then neither text contains `--`, `/-`, or a double quote
    And neither text contains the copied source phrase `natural number`

  @LN-04 @build
  Scenario: Generated Lean contains no sorry, admit, axiom, opaque, unsafe, native_decide, or placeholder declaration.
    Given the generated Lean for the nat-add-zero example and for the test.defs definitions fixture
    When each Lean text is searched for the six forbidden declaration spellings
    Then no sorry-, admit-, axiom-, opaque-, unsafe-, or native-decide-form token appears in either file

  @LN-05 @build
  Scenario: Every linked term and proof variant has one defined Lean lowering and missing lowering is a hard error.
    Given ten one- and two-theorem modules exercising assume, witness, left alternative, have, rewrite, simplify, constructor, induction, calculate, and apply proofs
    When each module is written to `src/Main.lex.tex`, checked, and rendered to Lean
    Then every module checks successfully
    And the concatenated Lean corpus contains `intro`, `exact`, `apply`, `rfl`, `refine`, `left`, `have`, `rw [`, `simp only [`, `constructor`, `induction`, and `calc`

  @LN-06 @build
  Scenario: Leading universal binders become deterministic declaration parameters with complete source mapping.
    Given the nat-add-zero example project rendered to Lean
    When the first module's Lean text is inspected for the peeled leading universal
    Then the declaration carries the parameter `(llv0 : Nat)`
    And no residual universal quantifier symbol remains in the text
    And the byte offset of `llv0` lies inside one Lean coverage row

  @LN-07 @build
  Scenario: All document definitions emit def and never alternate declaration forms.
    Given the test.defs definitions fixture with a type, a term, and a predicate definition
    When the fixture is rendered to Lean
    Then the `Main` module contains `def count`, `def double`, and `def good`
    And it contains none of `abbrev`, `instance `, `structure `, or `inductive `

  @LN-08 @build
  Scenario: Proof lowering uses only the fixed pinned Lean forms enumerated by the specification.
    Given the nat-add-zero example project rendered to Lean
    When the tactic block after `:= by` and before `end` is split into whitespace tokens
    Then every token is `rfl` or begins with `llv` or `llh`

  @LN-09 @build
  Scenario: Lean formatting is byte-deterministic with fixed indentation, LF, and final LF.
    Given the nat-add-zero example project
    When the `Main` module is rendered to Lean twice in one process
    Then both renderings are byte-identical
    And the text ends with a single final LF and contains no CR or tab
    And every line's leading space count is a multiple of two

  @LN-10 @build
  Scenario: Every non-whitespace generated Lean token has a source, glossary, IR, or synthetic-core mapping.
    Given the nat-add-zero example project rendered to Lean with its coverage rows
    When every non-whitespace byte of the `Main` Lean text is checked against the Lean coverage rows
    Then each such byte lies inside exactly one coverage row

  @LN-11 @build
  Scenario: The generated-source audit tokenizes and rejects prose-bearing or forbidden Lean tokens before verification.
    Given the shared verified run of the nat-add-zero example
    When the published build root is inspected after verification
    Then an `audit` directory exists inside the build root
    And the committed `tests/golden/axiom-parser/rejected.txt` corpus is nonempty

  @LN-12 @build
  Scenario: Generated file paths and module names exactly mirror the configured module prefix and source module.
    Given the nat-add-zero example project with `module_prefix = "LexLeanExample"`
    When the project is rendered, then relocked and rendered again with `module_prefix = "Other"`
    Then the first build's module is `LexLeanExample.Main` at `modules/LexLeanExample/Main.lean` with `namespace LexLeanExample.Main`
    And the second build's module path is `modules/Other/Main.lean` with `namespace Other.Main`
