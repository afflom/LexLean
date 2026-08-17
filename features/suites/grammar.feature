Feature: grammar

  The structural, phrase, mathematical-island, and proposition grammars (§15).

  @GR-01 @build
  Scenario: A source module parses only under the exact structural grammar and environment set.
    Given the example project with `\begin{theorem}{add-zero}` renamed to `\begin{conjecture}{add-zero}`
    When lexlean check runs
    Then it fails with LLL1004 because `conjecture` is not a lexlean environment
    And a second copy with `stray words` inserted before `\begin{theorem}` fails with LLP2003

  @GR-02 @build
  Scenario: Glossary imports, module imports, title, and blocks obey exact header order and cardinality.
    Given the example project with `\useglossary` moved after `\title` in `src/Main.lex.tex`
    When lexlean check runs
    Then it fails with LLP2003 for the out-of-order header
    And a copy with the `\title` line duplicated fails with LLP2003
    And a copy with the `\title` line removed fails with LLP2003

  @GR-03 @build
  Scenario: Sections nest within the configured scope limit and section parameters introduce explicit inherited context.
    Given a `Main` module whose `basics` section declares `\parameters{natural number \(n\)}` and states `\(n + 0 = n\)` inside it
    When lexlean check runs
    Then the section-parameter theorem `param-use` checks cleanly
    And with `max_scope_depth = 1` in `lexlean.toml` and a relocked project, an `inner` section nested inside `outer` fails with LLS8002

  @GR-04 @build
  Scenario: Titles and headings accept only bounded concept phrases and cannot encode an unproved proposition.
    Given the example project with `\title{Natural number addition}` replaced by `\title{\(N = N\)}`
    When lexlean check runs
    Then it fails with one of LLP2001, LLP2003, or LLT4001
    And no proposition-shaped title is accepted

  @GR-05 @build
  Scenario: Only parenthesized and display control delimiters create math islands; dollar math is rejected.
    Given the example project with `\(n + 0 = n\)` rewritten as `$n + 0 = n$`
    When lexlean check runs
    Then it fails with LLP2001 at the dollar-delimited math
    And the same statement written as display math `\[n + 0 = n\]` checks cleanly

  @GR-06 @build
  Scenario: Dynamic mathematical operators obey declared precedence, associativity, and explicit grouping.
    Given the example project with the theorem statement `\(n + n * n = n\)`
    When lexlean check runs and the Lean for `Main` is rendered
    Then the Lean contains `Nat.add llv0 (Nat.mul llv0 llv0)` so `*` binds tighter than `+`
    And the statement `\(n + n + n = n\)` renders as `Nat.add (Nat.add llv0 llv0) llv0` so `+` associates left
    And the unparenthesized chain `\(n = n = n\)` fails with LLP2004 because `=` is nonassociative

  @GR-07 @build
  Scenario: Mathematical juxtaposition is never interpreted as implicit multiplication or application.
    Given the example project with the theorem statement `\(n n = n\)`
    When lexlean check runs
    Then it fails with LLP2004 or LLP2001
    And juxtaposed `n n` is given no multiplication or application reading

  @GR-08 @build
  Scenario: Universal, existential, unique-existential, conditional, and connective proposition forms have the specified compositional semantics.
    Given a `Main` module stating `For every natural number \(n\), if <condition>, then \(n + 0 = n\)` with an `Assume \(h\)` reflexivity proof
    When lexlean check runs for each condition and the Lean for `Main` is rendered
    Then `\(n = n\) and \(n = 0\)` lowers to `And`, `or` lowers to `Or`, and `not \(n = 0\)` lowers to `Not`
    And `there exists a natural number \(k\) such that \(k = 0\)` lowers to `Exists`
    And `there exists exactly one natural number \(k\) such that \(k = 0\)` lowers to `ExistsUnique`
    And the universal becomes the parameter `(llv0 : Nat)` and the conditional becomes an arrow

  @GR-09 @build
  Scenario: Proposition precedence and associativity produce the specified parse or an ambiguity error.
    Given a `Main` module whose conditional hypothesis is `\(n = n\) and \(n = 0\) or \(n = 0\)`
    When lexlean check runs and the Lean for `Main` is rendered
    Then the `Or` node appears before the `And` node in the Lean text
    And `P and Q or R` therefore parses as `Or(And(P,Q),R)`

  @GR-10 @build
  Scenario: Articles, plural forms, capitalization, and inflections are explicit lexicon data rather than inferred language rules.
    Given the example project with `For every natural number` changed to `For every natural numbers`
    When lexlean check runs
    Then it fails with LLP2001 or LLL1004 because a plural in a singular slot has no inferred reading
    And the entry `language/std/nat/entries/nat.toml` spells out `article-a`, `plural`, `sentence-case`, and `singular` as explicit data

  @GR-11 @build
  Scenario: A component with no complete grammar parse fails with a bounded structured diagnostic.
    Given the example project with the theorem statement replaced by `For every natural number \(n\), such that.`
    When lexlean check runs
    Then the first diagnostic has code LLP2001 and carries a primary span
    And its message is shorter than 1000 characters
    And at most 256 diagnostics are reported

  @GR-12 @build
  Scenario: Distinct surviving parses fail as ambiguity while semantically identical canonical IR alternatives collapse.
    Given lexicons `test.dupa` and `test.dupb` that both give surface `nzz` with different denotations `Nat.le_refl` and `Nat.ge_refl`
    When lexlean check runs on the relocked `nzz` module importing both
    Then it fails with LLP2002 for the two distinct surviving parses
    And a single `test.dupa` entry with two forms `nzz` and `nzz-alt` sharing surface `nzz` checks cleanly because both candidates elaborate to identical IR

  @GR-13 @build
  Scenario: Free expository paragraphs and opaque text nodes are rejected.
    Given the example project with `This is obvious.` inserted before `\begin{proof}`
    When lexlean check runs
    Then it fails with LLP2003 or LLF5005 for the expository sentence inside the theorem
    And the same sentence inserted before `\begin{theorem}` fails with LLP2003
    And the statement replaced by `\text{obvious}` fails with LLL1004

  @GR-14 @build
  Scenario: Definition and theorem-like components enforce exact sentence, policy, and proof cardinalities.
    Given the example project with a second `\begin{proof}...\end{proof}` block appended inside the theorem
    When lexlean check runs
    Then it fails with LLP2003 for the extra proof
    And a copy with the `\noaxioms` policy line removed fails with LLP2003

  @GR-15 @build
  Scenario: Explicit module imports form an acyclic graph and selected builds include their transitive closure.
    Given the example project with a `Helper` module and `\importmodule{Helper}` added to `Main`
    When lexlean check runs
    Then the checked unit set is exactly `Helper` and `Main`
    And adding `\importmodule{Main}` to `Helper` makes the check fail with LLR3003 for the import cycle

  @GR-16 @build
  Scenario: A same-module declaration cannot reference a later declaration.
    Given a `Main` module whose theorem `first` closes its goal with `\reference{Main::second}` declared after it
    When lexlean check runs
    Then it fails with LLR3005 for the forward reference
    And the mirror module where `second` references the earlier `Main::first` checks cleanly
