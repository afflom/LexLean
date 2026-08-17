Feature: latex-pdf

  Canonical LaTeX rendering, output coverage, and the external PDF protocol (§19).

  @TX-01 @build
  Scenario: Canonical LaTeX is rendered solely from linked IR and never copies source text or controls.
    Given the nat-add-zero example project whose source proof reads `Close the goal by reflexivity.`
    When the `Main` module is rendered to canonical LaTeX twice
    Then both renderings are identical
    And the source spelling `Close the goal by reflexivity` does not appear in the output
    And the generated proof sentence `The goal follows by reflexivity.` does

  @TX-02 @build
  Scenario: Every module uses the exact canonical LaTeX preamble and no host or timestamp metadata.
    Given the nat-add-zero example project rendered to canonical LaTeX
    When the `Main` module text is compared against the section 29.4 preamble
    Then the text begins with the exact preamble from `\documentclass[11pt]{article}` through `\begin{document}`
    And it contains none of `\today`, `\date`, or `hostname`

  @TX-03 @build
  Scenario: Statements use only canonical controlled proposition and definition renderings.
    Given the nat-add-zero example project rendered to canonical LaTeX
    When the theorem statement of `Main` is located
    Then it reads exactly `For every natural number \(n\), \(n + 0 = n\).`

  @TX-04 @build
  Scenario: Proof prose is generated from proof IR using fixed core lexical forms.
    Given the nat-add-zero example project rendered to canonical LaTeX
    When the proof environment of `Main` is located
    Then it is exactly `\begin{proof}` followed by `The goal follows by reflexivity.` and `\end{proof}` on three lines

  @TX-05 @build
  Scenario: Titles, sections, parameters, environments, numbering, and labels follow the exact document rules.
    Given the nat-add-zero example project rendered to canonical LaTeX
    When the `Main` document structure is checked against section 29.4
    Then it contains a centered `{\LARGE Natural number addition}` title block
    And `\begin{theorem}` is immediately followed by `\label{ll:main:add-zero}`
    And it declares `\newtheorem{theorem}{Theorem}[section]` and closes with `\end{document}`

  @TX-06 @build
  Scenario: Every visible LaTeX word, symbol, punctuation mark, and control has complete coverage.
    Given the nat-add-zero example project rendered with its LaTeX coverage rows
    When every non-whitespace byte of the `Main` canonical LaTeX is checked against the LaTeX coverage rows
    Then each such byte lies inside exactly one coverage row

  @TX-07 @build
  Scenario: Non-core lexicons cannot inject a raw TeX control or unclassified output segment.
    Given a `test.evil` fixture lexicon whose `evil` entry renders as `(token write18)`
    When the package is registered as a path source and lexlean lock runs
    Then locking fails
    And the diagnostic code is LLR3004

  @TX-08 @build
  Scenario: Canonical LaTeX bytes are deterministic, LF-normalized, and final-LF terminated.
    Given the nat-add-zero example project
    When the `Main` module is rendered to canonical LaTeX twice
    Then the text ends with a final LF and contains no CR
    And the two renderings are byte-identical

  @TX-09 @build
  Scenario: An enabled external PDF provider runs without a shell in an isolated directory with exact hashes and resources.
    Given a shell-script fake PDF provider at `tools/fakepdf` that records its working directory and directory listing into the PDF
    When the provider is run with a wrong `program_sha256` and then again with the correct hash
    Then the wrong hash is refused before execution with LLS8004
    And the correct run produces a `%PDF-` stream from a `.lexlean/.../work` directory distinct from the project root
    And the provider's directory listing is exactly `LexLeanExample.Main.tex`

  @TX-10 @build
  Scenario: The PDF recipe ID and actual PDF hash use the specified independent content records.
    Given the fake PDF provider run over the rendered `Main` module
    When the recipe ID is recomputed from `lexlean-pdf-recipe-v1` with framed `tex`, `program`, `version-output`, `argv`, and `resources` records
    Then the recomputed digest equals the returned recipe ID
    And the returned `pdf_sha256` equals the sha256 of the PDF bytes
    And the recipe ID and PDF hash differ

  @TX-11 @build
  Scenario: PDF success or failure never changes mathematical verification authority.
    Given a fake PDF provider that exits with status 1
    When the provider is run and separately a `[pdf]` external section is added to `lexlean.toml` and the project relocked
    Then the failing run yields diagnostic LLB6004
    And the semantic ID of the project with the `[pdf]` section equals the semantic ID without it

  @TX-12 @build
  Scenario: The publishable document is the canonical renderer output rather than unchecked source bytes.
    Given the nat-add-zero example project
    When lexlean build runs and `manifest.json` under the build directory is parsed
    Then the outputs list contains `modules/LexLeanExample/Main.tex`
    And the outputs list does not contain `src/Main.lex.tex`
