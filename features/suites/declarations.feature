Feature: declarations

  Definition sentences, theorem-like components, and axiom policies (§15.7-§15.9, §18.6).

  @DF-01 @build
  Scenario: A valid type-definition sentence emits one nonrecursive sort-valued Lean def linked to its document entry.
    Given the `test.defs` project whose typedefinition `count` says `A count is defined as \(N\)`
    When lexlean check runs and the Lean for `Main` is rendered
    Then the Lean contains `def count : Type :=` followed by `Nat`
    And the linked `count` declaration is a Definition whose entry is `test.defs::count`

  @DF-02 @build
  Scenario: A valid term-definition sentence emits one nonrecursive explicitly typed Lean def.
    Given the `test.defs` project whose termdefinition says `\(double(n)\) is defined as \(n + n\)`
    When the Lean for `Main` is rendered
    Then it contains a `def double` line
    And that line carries the explicit result type `: Nat :=`

  @DF-03 @build
  Scenario: A valid predicate-definition sentence emits one nonrecursive Prop-valued Lean def.
    Given the `test.defs` project whose predicatedefinition `good` holds exactly when some `\(k = k\)`
    When the Lean for `Main` is rendered
    Then the `def good` line ends its signature with `: Prop :=`

  @DF-04 @build
  Scenario: Self recursion, mutual recursion, and later-declaration references are rejected.
    Given the `test.defs` project with `double(n)` redefined as `\(double(n) + n\)`
    When lexlean check runs
    Then it fails with one of LLF5001, LLR3003, or LLR3005 for the self recursion
    And moving the `good` predicate before `count` and making it use the not-yet-declared `double(k)` fails with LLR3005 or LLF5001

  @DF-05 @build
  Scenario: A definition's self head, explicit arguments, and signature order are checked exactly.
    Given the `test.defs` project with the self head written as `\(double(n, n)\)`
    When lexlean check runs
    Then it fails with LLF5001 for the wrong explicit argument count
    And a copy whose self head is `\(double(m)\)` under the binder `n` also fails with LLF5001

  @DF-06 @build
  Scenario: Every generated definition and theorem-like declaration carries one explicit axiom policy.
    Given the `test.defs` project with the `\noaxioms` line removed from the `count` typedefinition
    When lexlean check runs
    Then it fails with LLP2003 for the missing axiom policy
    And the unmodified project's canonical linked JSON records a `"policy"` on every declaration

  @DF-07 @build
  Scenario: Theorem, lemma, and corollary each emit Lean theorem declarations while retaining distinct document metadata.
    Given the example project with `theorem` `add-zero` rewritten as a `lemma`
    When lexlean check runs and the build for `Main` is rendered
    Then the Lean contains `theorem add_zero`
    And the canonical LaTeX keeps `\begin{lemma}`
    And the linked declaration kind is `Lemma`

  @DF-08 @build
  Scenario: Author-defined axioms, opaque declarations, and proofless theorem-like components are rejected.
    Given the example project with the theorem environment renamed to `axiom`
    When lexlean check runs
    Then it fails with LLL1004 because `axiom` is not an accepted environment
    And a copy with the whole `\begin{proof}...\end{proof}` block deleted fails with LLF5005

  @DF-09 @build
  Scenario: Every theorem-like component contains exactly one nonempty structured proof.
    Given the example project with an empty `\begin{proof}\end{proof}` body
    When lexlean check runs
    Then it fails with one of LLF5004, LLF5003, or LLF5005
    And a copy with two reflexivity proofs in one theorem fails with LLP2003

  @DF-10 @build
  Scenario: Generated declarations preserve source order and every document reference respects that order.
    Given the `test.defs` project declaring `count`, `double`, `good`, then `add-zero`
    When the Lean for `Main` is rendered
    Then `def count`, `def double`, `def good`, and `theorem add_zero` appear in that source order
