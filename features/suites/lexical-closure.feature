Feature: lexical-closure

  Source normalization, the primitive scanner, and closed lexical resolution (§12, §14).

  @LX-01 @build
  Scenario: Source decoding and line normalization enforce valid UTF-8, LF, final LF, and forbidden-scalar rules.
    Given four example copies whose src/Main.lex.tex has an 0xFF byte, a NUL before \title, its final LF trimmed, and a UTF-8 BOM prepended
    When `lexlean check` runs on each
    Then the invalid UTF-8 copy fails with LLL1001
    And the NUL and unterminated copies fail with LLL1001
    And the BOM copy fails with LLL1001

  @LX-02 @build
  Scenario: Non-NFC source is diagnosed and canonical formatting rewrites it without semantic change.
    Given the example project with the title word `addition` spelled with a decomposed n plus combining tilde
    When `lexlean check` runs and then normalize runs in fmt mode on a `\title{}` line with the same sequence
    Then check fails with LLL1003
    And the fmt-mode output contains the composed U+00F1 character

  @LX-03 @build
  Scenario: Raw percent, comments, tabs, trailing spaces, and non-ASCII whitespace are rejected.
    Given four example copies with `% comment` before `For every`, a tab before `For every`, a trailing space after `\(n + 0 = n\).`, and U+00A0 inside `For every`
    When `lexlean check` runs on each
    Then the percent comment fails with LLL1002
    And the tab fails with LLL1002
    And the trailing space and the non-ASCII space fail with LLL1001

  @LX-04 @build
  Scenario: The primitive scanner recognizes exactly the specified atom classes and records exact spans.
    Given the text `\begin{lexlean}{Main}` followed by a line `text 12 + U+2115`
    When lexlean::source::scan::scan tokenizes it
    Then the atoms are Control, Delimiter, Word, Delimiter, Delimiter, Word, Delimiter, Whitespace, Word, Whitespace, Numeral, Whitespace, AsciiSymbol, Whitespace, UnicodeSymbol, Whitespace with those exact texts
    And consecutive atom spans are contiguous from byte 0 to the end of the text

  @LX-05 @build
  Scenario: Core braces, controls, punctuation, and grammar tokens receive glossary coverage rather than TeX trust.
    Given the example project checked into a CheckedProject
    When the coverage_source rows of module Main are matched to the `\begin` atom and to a `{` atom
    Then `\begin` is covered by Origin::Structural with package lexlean.core and entry begin
    And the brace atom has a coverage row starting at its byte offset

  @LX-06 @build
  Scenario: An undeclared prose word is rejected with an exact unknown-atom diagnostic.
    Given the example project with `banana` inserted into the theorem statement after `For every`
    When `lexlean check` runs
    Then it fails with LLL1004
    And the primary span of that diagnostic covers exactly the bytes of `banana`

  @LX-07 @build
  Scenario: An undeclared symbol or control sequence is rejected with an exact unknown-atom diagnostic.
    Given one example copy with `\mystery{}` before `For every` and another with U+2297 replacing `+` in `\(n + 0 = n\)`
    When `lexlean check` runs on each
    Then the unknown control fails with LLL1004
    And the unknown symbol fails with LLL1004

  @LX-08 @build
  Scenario: Lexical analysis builds all valid form edges without greedy import-order selection.
    Given two projects with packages test.dupa and test.dupb both defining nzz, one importing dupa before dupb and the other dupb before dupa
    When `lexlean check` runs on each ordering
    Then both fail with LLP2002
    And the LLP2002 message is identical for the two import orders

  @LX-09 @build
  Scenario: Every accepted non-whitespace source atom is covered exactly once in the selected path.
    Given the example project checked into a CheckedProject
    When every non-Whitespace atom of module Main is matched against the coverage_source rows
    Then each such atom lies inside exactly one coverage row

  @LX-10 @build
  Scenario: A local identifier is accepted only when introduced by a binder and every later occurrence resolves by scope.
    Given the example project with `\(n + 0 = n\)` changed to `\(n + 0 = m\)`
    When `lexlean check` runs on it and on the untouched example
    Then the unbound `m` fails with LLP2002, LLL1004, or LLT4001
    And the untouched example with binder-introduced `n` checks cleanly

  @LX-11 @build
  Scenario: TeX macro definition, expansion, file access, and execution controls are rejected even if a package declares them.
    Given example copies with `\def` and `\input{other}` inserted before `For every`, and a package test.smuggle whose evil.toml form has surface `\def`
    When `lexlean check` runs on the two source copies and lock runs on the smuggler
    Then `\def` fails with LLL1004
    And `\input{other}` fails with LLL1004
    And the package declaring `\def` fails lock with LLR3004

  @LX-12 @build
  Scenario: Qualified lexeme and document-reference controls select only existing closed entries or declarations.
    Given example copies using `\lexeme{lexlean.std.nat::zero}`, `\lexeme{lexlean.std.nat::missing}`, and `\reference{Main::absent}`
    When `lexlean check` runs on each
    Then the existing qualified lexeme checks cleanly
    And the missing lexeme fails with LLR3005
    And the dangling document reference fails with LLR3005

  @LX-13 @build
  Scenario: Lexical or semantic ambiguity is rejected and no priority or heuristic chooses a candidate.
    Given the example project importing test.dupa and test.dupb which both define nzz
    When `lexlean check` runs
    Then it fails with LLP2002
    And the LLP2002 diagnostic names both dupa and dupb

  @LX-14 @build
  Scenario: Canonical formatting chooses safe canonical forms and proves linked-IR preservation.
    Given the committed example and a copy with two extra blank lines before `\begin{theorem}`
    When fmt --check runs on the committed copy, the padded copy is checked, formatted, and checked again
    Then the committed source passes fmt --check
    And the padded copy's semantic_id equals the committed one before and after formatting
    And formatting rewrites the padded source to the committed bytes
