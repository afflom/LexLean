//! The `grammar` suite: GR-01..GR-16.

use crate::support::{self, P};

/// The example with one replacement in `src/Main.lex.tex`.
fn mutated(from: &str, to: &str) -> P {
    let project = P::example();
    project.edit("src/Main.lex.tex", from, to);
    project
}

/// A module statement wrapped as `If P, then Q` over a bound local, with an
/// `Assume`-then-reflexivity proof.
fn conditional_module(condition: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{shape}}\n\\noaxioms\nFor every natural number \\(n\\), if {condition}, then \\(n + 0 = n\\).\n\\begin{{proof}}\nAssume \\(h\\).\nClose the goal by reflexivity.\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

fn conditional_project(condition: &str) -> P {
    let project = P::example();
    project.write("src/Main.lex.tex", &conditional_module(condition));
    project
}

/// The generated Lean for a proposition-form fixture.
fn lean_for_condition(condition: &str) -> String {
    let project = conditional_project(condition);
    project.check_ok();
    support::lean_text(&support::rendered(&project), "Main")
}

pub(crate) fn run(id: &str) {
    match id {
        // §15.1: only the fixed environment set parses.
        "GR-01" => {
            mutated(
                "\\begin{theorem}{add-zero}",
                "\\begin{conjecture}{add-zero}",
            )
            .check_fails_with("LLL1004");
            mutated("\\begin{theorem}", "stray words\n\\begin{theorem}")
                .check_fails_with("LLP2003");
        }
        // §15.1, GR-02: exact header order and cardinality.
        "GR-02" => {
            let late_glossary = mutated(
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}",
                "\\title{Natural number addition}\n\\useglossary{lexlean.std.nat@1.0.0}",
            );
            late_glossary.check_fails_with("LLP2003");

            mutated(
                "\\title{Natural number addition}",
                "\\title{Natural number addition}\n\\title{Natural number addition}",
            )
            .check_fails_with("LLP2003");

            mutated("\\title{Natural number addition}\n", "").check_fails_with("LLP2003");
        }
        // §15.1: nesting bounded by the configured scope limit; parameters
        // introduce explicit inherited context.
        "GR-03" => {
            let sectioned = P::example();
            sectioned.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{section}{basics}\n\\heading{Natural number addition}\n\\parameters{natural number \\(n\\)}\n\\begin{theorem}{param-use}\n\\noaxioms\n\\(n + 0 = n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{section}\n\\end{lexlean}\n",
            );
            sectioned.check_ok();

            let deep = P::example();
            deep.edit(
                "lexlean.toml",
                "max_scope_depth = 1024",
                "max_scope_depth = 1",
            );
            deep.relock();
            deep.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{section}{outer}\n\\heading{Natural number addition}\n\\begin{section}{inner}\n\\heading{Natural number addition}\n\\end{section}\n\\end{section}\n\\end{lexlean}\n",
            );
            deep.check_fails_with("LLS8002");
        }
        // §15.3: titles and headings cannot encode a proposition.
        "GR-04" => {
            let error =
                mutated("\\title{Natural number addition}", "\\title{\\(ℕ = ℕ\\)}").check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2001" | "LLP2003" | "LLT4001")),
                "a title cannot encode a proposition: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §15.5: only \( \) and \[ \] make islands; dollars are rejected.
        "GR-05" => {
            mutated("\\(n + 0 = n\\)", "$n + 0 = n$").check_fails_with("LLP2001");
            mutated("\\(n + 0 = n\\)", "\\[n + 0 = n\\]").check_ok();
        }
        // §15.5: declared precedence and associativity govern operators.
        "GR-06" => {
            let precedence = mutated("\\(n + 0 = n\\)", "\\(n + n * n = n\\)");
            precedence.check_ok();
            let lean = support::lean_text(&support::rendered(&precedence), "Main");
            assert!(
                lean.contains("Nat.add llv0 (Nat.mul llv0 llv0)"),
                "* binds tighter than +, found: {lean}"
            );

            let associativity = mutated("\\(n + 0 = n\\)", "\\(n + n + n = n\\)");
            associativity.check_ok();
            let lean = support::lean_text(&support::rendered(&associativity), "Main");
            assert!(
                lean.contains("Nat.add (Nat.add llv0 llv0) llv0"),
                "+ associates left, found: {lean}"
            );

            // `=` is nonassociative: an unparenthesized chain is an error.
            mutated("\\(n + 0 = n\\)", "\\(n = n = n\\)").check_fails_with("LLP2004");
        }
        // §15.5: juxtaposition is never multiplication or application.
        "GR-07" => {
            let error = mutated("\\(n + 0 = n\\)", "\\(n n = n\\)").check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2004" | "LLP2001")),
                "juxtaposition has no reading: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §15.6: the compositional semantics of every proposition form.
        "GR-08" => {
            let and = lean_for_condition("\\(n = n\\) and \\(n = 0\\)");
            assert!(and.contains("And"), "conjunction lowers to And: {and}");
            let or = lean_for_condition("\\(n = n\\) or \\(n = 0\\)");
            assert!(or.contains("Or"), "disjunction lowers to Or: {or}");
            let not = lean_for_condition("not \\(n = 0\\)");
            assert!(not.contains("Not"), "negation lowers to Not: {not}");
            let exists =
                lean_for_condition("there exists a natural number \\(k\\) such that \\(k = 0\\)");
            assert!(
                exists.contains("Exists"),
                "existential lowers to Exists: {exists}"
            );
            let unique = lean_for_condition(
                "there exists exactly one natural number \\(k\\) such that \\(k = 0\\)",
            );
            // The IR keeps `ExistsUnique`; the printed Lean is its documented
            // expansion (Lean 4.32.1 has no `ExistsUnique` constant).
            assert!(
                unique.contains("Exists (fun (llv1 : Nat) => And (Eq llv1 (0 : Nat)) ((llv2 : Nat) → (Eq llv2 (0 : Nat)) → Eq llv2 llv1))"),
                "unique existence lowers to the ExistsUnique expansion: {unique}"
            );
            // The conditional itself is a Pi/arrow with the universal binder
            // peeled to a parameter.
            assert!(
                and.contains("(llv0 : Nat)") && (and.contains("->") || and.contains("\u{2192}")),
                "universals become parameters and conditionals become arrows: {and}"
            );
        }
        // §15.6: fixed precedence yields one parse; `and` binds under `or`.
        "GR-09" => {
            let lean = lean_for_condition("\\(n = n\\) and \\(n = 0\\) or \\(n = 0\\)");
            let or_at = lean.find("Or").expect("an Or node");
            let and_at = lean.find("And").expect("an And node");
            assert!(
                and_at > or_at,
                "`P and Q or R` parses as Or(And(P,Q),R): {lean}"
            );
        }
        // §13.5: articles, plurals, and capitalization are lexicon data.
        "GR-10" => {
            let error =
                mutated("For every natural number", "For every natural numbers").check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2001" | "LLL1004")),
                "a plural form in a singular slot has no inferred reading: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
            let nat_entry = std::fs::read_to_string(
                support::repo_root()
                    .join("language/std/nat/entries/nat.toml")
                    .as_std_path(),
            )
            .expect("nat entry");
            for datum in ["article-a", "plural", "sentence-case", "singular"] {
                assert!(
                    nat_entry.contains(datum),
                    "inflection `{datum}` is explicit lexicon data"
                );
            }
        }
        // §15.6: a failed parse is a bounded structured diagnostic.
        "GR-11" => {
            let error = mutated(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "For every natural number \\(n\\), such that.",
            )
            .check_err();
            let diagnostic = error.diagnostics.first().expect("a structured diagnostic");
            assert_eq!(diagnostic.code.as_str(), "LLP2001");
            assert!(diagnostic.primary.is_some(), "the diagnostic has a span");
            assert!(
                diagnostic.message.len() < 1_000,
                "the diagnostic is bounded, not a dump"
            );
            assert!(
                error.diagnostics.len() <= 256,
                "diagnostics respect max_diagnostics"
            );
        }
        // §14.4: distinct parses are ambiguity; identical IR collapses.
        "GR-12" => {
            let distinct = P::example();
            distinct.add_package(
                "lexicons/test-dupa",
                "test.dupa",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[
                    ("nzz.toml", &support::nzz_entry("Nat.le_refl")),
                    ("z.toml", Z_LOCAL),
                ],
            );
            distinct.add_package(
                "lexicons/test-dupb",
                "test.dupb",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("nzz.toml", &support::nzz_entry("Nat.ge_refl"))],
            );
            distinct.write(
                "src/Main.lex.tex",
                &support::nzz_module(&["test.dupa@1.0.0", "test.dupb@1.0.0"]),
            );
            distinct.relock();
            distinct.check_fails_with("LLP2002");

            // Two forms of one entry share a surface: both candidates
            // elaborate to the same linked IR and collapse (§14.4).
            let collapsing = P::example();
            let doubled_form = support::nzz_entry("Nat.le_refl").replace(
                "[render]",
                "[[form]]\nid = \"nzz-alt\"\nchannel = \"math\"\nsurface = \"nzz\"\ncanonical_source = false\nfeatures = []\n\n[render]",
            );
            collapsing.add_package(
                "lexicons/test-dupa",
                "test.dupa",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("nzz.toml", &doubled_form), ("z.toml", Z_LOCAL)],
            );
            collapsing.write(
                "src/Main.lex.tex",
                &support::nzz_module(&["test.dupa@1.0.0"]),
            );
            collapsing.relock();
            collapsing.check_ok();
        }
        // §15.6: free expository text and opaque nodes are rejected.
        "GR-13" => {
            let error = mutated("\\begin{proof}", "This is obvious.\n\\begin{proof}").check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2003" | "LLF5005")),
                "expository prose inside a component is rejected: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
            mutated("\\begin{theorem}", "This is obvious.\n\\begin{theorem}")
                .check_fails_with("LLP2003");
            mutated("\\(n + 0 = n\\)", "\\text{obvious}").check_fails_with("LLL1004");
        }
        // §15.8: exact sentence, policy, and proof cardinalities.
        "GR-14" => {
            mutated(
                "\\end{proof}\n\\end{theorem}",
                "\\end{proof}\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}",
            )
            .check_fails_with("LLP2003");
            mutated("\\noaxioms\n", "").check_fails_with("LLP2003");
        }
        // §15.1: module imports are acyclic; closure is included.
        "GR-15" => {
            let project = P::example();
            project.write(
                "src/Helper.lex.tex",
                "\\begin{lexlean}{Helper}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{helper-fact}\n\\noaxioms\nFor every natural number \\(m\\), \\(m + 0 = m\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n",
            );
            project.edit(
                "src/Main.lex.tex",
                "\\useglossary{lexlean.std.nat@1.0.0}",
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\importmodule{Helper}",
            );
            let checked = project.check_ok();
            assert_eq!(
                checked.units.keys().cloned().collect::<Vec<_>>(),
                vec!["Helper".to_owned(), "Main".to_owned()],
                "the transitive import closure is part of the result set"
            );

            project.edit(
                "src/Helper.lex.tex",
                "\\useglossary{lexlean.std.nat@1.0.0}",
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\importmodule{Main}",
            );
            project.check_fails_with("LLR3003");
        }
        // §15.1: no same-module reference to a later declaration.
        "GR-16" => {
            let forward = P::example();
            forward.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{first}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal with \\(\\reference{Main::second}\\).\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{second}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n",
            );
            forward.check_fails_with("LLR3005");

            let backward = P::example();
            backward.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{first}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{second}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal with \\(\\reference{Main::first}\\).\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n",
            );
            backward.check_ok();
        }
        other => panic!("no grammar case is wired for {other}"),
    }
}

/// The math-channel zero used by the duplicate fixtures.
const Z_LOCAL: &str = r#"spec = "lexlean/entry/1"
id = "z"
category = "term-constant"
signature = "(const lexlean.std.nat::nat)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.zero"

[[form]]
id = "z"
channel = "both"
surface = "z"
canonical_source = true
features = []

[render]
math = "(operator-name z)"
"#;
