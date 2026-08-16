//! The `proofs` suite: PF-01..PF-18.

use crate::support::{self, P};

/// A one-theorem module with the given statement and proof body.
fn theorem_module(statement: &str, proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{main-goal}}\n\\noaxioms\n{statement}\n\\begin{{proof}}\n{proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

/// A two-theorem module: `first` (proved by reflexivity) then `second`.
fn two_theorems(first_statement: &str, second_statement: &str, second_proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{first}}\n\\noaxioms\n{first_statement}\n\\begin{{proof}}\nClose the goal by reflexivity.\n\\end{{proof}}\n\\end{{theorem}}\n\n\\begin{{theorem}}{{second}}\n\\noaxioms\n{second_statement}\n\\begin{{proof}}\n{second_proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

/// Two theorems where `first` is a conditional proved by Assume, so its
/// application yields statically determined residual premises.
fn conditional_lemma_pair(
    first_statement: &str,
    second_statement: &str,
    second_proof: &str,
) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{first}}\n\\noaxioms\n{first_statement}\n\\begin{{proof}}\nAssume \\(h\\).\nClose the goal by reflexivity.\n\\end{{proof}}\n\\end{{theorem}}\n\n\\begin{{theorem}}{{second}}\n\\noaxioms\n{second_statement}\n\\begin{{proof}}\n{second_proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

fn project_with(module: &str) -> P {
    let project = P::example();
    project.write("src/Main.lex.tex", module);
    project
}

/// Check a module and return its generated Lean.
fn lean_of(module: &str) -> String {
    let project = project_with(module);
    project.check_ok();
    support::lean_text(&support::rendered(&project), "Main")
}

/// Check a module, expecting a proof-family failure code from the list.
fn fails_within(module: &str, codes: &[&str]) {
    let error = project_with(module).check_err();
    assert!(
        error
            .diagnostics
            .iter()
            .any(|d| codes.contains(&d.code.as_str())),
        "expected one of {codes:?}, found {:?}",
        error
            .diagnostics
            .iter()
            .map(|d| d.code.as_str())
            .collect::<Vec<_>>()
    );
}

pub(crate) fn run(id: &str) {
    match id {
        // §16.2: Assume introduces scoped locals; Close-with is exact.
        "PF-01" => {
            let lean = lean_of(&theorem_module(
                "For every natural number \\(n\\), if \\(n = n\\), then \\(n + 0 = n\\).",
                "Assume \\(h\\).\nClose the goal by reflexivity.",
            ));
            assert!(lean.contains("intro"), "Assume lowers to intro: {lean}");

            let lean = lean_of(&two_theorems(
                "\\(0 + 0 = 0\\).",
                "\\(0 + 0 = 0\\).",
                "Close the goal with \\(\\reference{Main::first}\\).",
            ));
            assert!(lean.contains("exact"), "Close-with lowers to exact: {lean}");
        }
        // §16.2: simple Apply needs exactly one residual premise.
        "PF-02" => {
            let lean = lean_of(&conditional_lemma_pair(
                "If \\(0 + 0 = 0\\), then \\(0 * 0 = 0\\).",
                "\\(0 * 0 = 0\\).",
                "Apply \\(\\reference{Main::first}\\).\nClose the goal by reflexivity.",
            ));
            assert!(lean.contains("apply"), "Apply lowers to apply: {lean}");

            fails_within(
                &conditional_lemma_pair(
                    "If \\(0 + 0 = 0\\), then if \\(0 * 0 = 0\\), then \\(0 - 0 = 0\\).",
                    "\\(0 - 0 = 0\\).",
                    "Apply \\(\\reference{Main::first}\\).\nClose the goal by reflexivity.",
                )
                .replace("Assume \\(h\\).", "Assume \\(h\\).\nAssume \\(g\\)."),
                &["LLF5002", "LLF5003"],
            );
        }
        // §16.6: structured apply names every premise once, in order.
        "PF-03" => {
            let module = conditional_lemma_pair(
                "If \\(0 + 0 = 0\\), then if \\(0 * 0 = 0\\), then \\(0 - 0 = 0\\).",
                "\\(0 - 0 = 0\\).",
                "\\begin{apply}{\\reference{Main::first}}\n\\begin{premise}{1}\nClose the goal by reflexivity.\n\\end{premise}\n\\begin{premise}{2}\nClose the goal by reflexivity.\n\\end{premise}\n\\end{apply}",
            )
            .replace(
                "Assume \\(h\\).",
                "Assume \\(h\\).\nAssume \\(g\\).",
            );
            let lean = lean_of(&module);
            assert!(
                lean.contains("apply"),
                "structured apply lowers to apply: {lean}"
            );

            fails_within(
                &module.replacen("{premise}{1}", "{premise}{2}", 1),
                &["LLF5003", "LLP2003"],
            );
        }
        // §16.2: Reflexivity is exactly pinned rfl and closes the goal.
        "PF-04" => {
            let build = support::rendered(&P::example());
            let lean = support::lean_text(&build, "Main");
            assert!(
                lean.contains("by\n  rfl"),
                "reflexivity lowers to exactly rfl: {lean}"
            );
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Close the goal by reflexivity.\nClose the goal by reflexivity.",
                ),
                &["LLF5002"],
            );
        }
        // §16.2: witness supplies the next existential witness only.
        "PF-05" => {
            let lean = lean_of(&theorem_module(
                "There exists a natural number \\(k\\) such that \\(k + 0 = k\\).",
                "Use \\(0\\) as the witness.\nClose the goal by reflexivity.",
            ));
            assert!(
                lean.contains("refine") && lean.contains("?_"),
                "the witness lowers to the pinned refine form: {lean}"
            );
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Use \\(0\\) as the witness.\nClose the goal by reflexivity.",
                ),
                &["LLF5002"],
            );
        }
        // §16.2: Left/Right select the disjunction constructor.
        "PF-06" => {
            let lean = lean_of(&theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\) or \\(n = 1\\).",
                "Select the left alternative.\nClose the goal by reflexivity.",
            ));
            assert!(lean.contains("left"), "Select-left lowers to left: {lean}");
            let lean = lean_of(&theorem_module(
                "For every natural number \\(n\\), \\(n = 1\\) or \\(n + 0 = n\\).",
                "Select the right alternative.\nClose the goal by reflexivity.",
            ));
            assert!(
                lean.contains("right"),
                "Select-right lowers to right: {lean}"
            );
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Select the left alternative.\nClose the goal by reflexivity.",
                ),
                &["LLF5002"],
            );
        }
        // §16.3: have establishes, then scopes the fresh hypothesis.
        "PF-07" => {
            let lean = lean_of(&theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{have}{h}\n\\(n + 0 = n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{have}\nClose the goal with \\(h\\).",
            ));
            assert!(
                lean.contains("have") && lean.contains(":= by"),
                "have lowers to the pinned form: {lean}"
            );
            // The hypothesis does not leak backward: using it before the
            // have fails.
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Close the goal with \\(h\\).",
                ),
                &["LLP2002", "LLL1004", "LLT4001", "LLF5002"],
            );
        }
        // §16.4: every rule, in source order, directed, at one target.
        "PF-08" => {
            let lean = lean_of(&two_theorems(
                "For every natural number \\(m\\), \\(m + 0 = m\\).",
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{rewrite}{goal}\n\\forward{\\reference{Main::first}}\n\\backward{\\reference{Main::first}}\n\\end{rewrite}\nClose the goal by reflexivity.",
            ));
            let rw_at = lean.find("rw [").expect("a rw step");
            let arrow_at = lean.find('\u{2190}').expect("the reversed rule");
            assert!(
                arrow_at > rw_at,
                "rules keep source order with explicit direction: {lean}"
            );
            // A non-equation rule is rejected.
            fails_within(
                &two_theorems(
                    "For every natural number \\(m\\), \\(m + 0 = m\\) or \\(m = 1\\).",
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{rewrite}{goal}\n\\forward{\\reference{Main::first}}\n\\end{rewrite}\nClose the goal by reflexivity.",
                ),
                &["LLF5002"],
            );
        }
        // §16.5: simplify is simp only with exactly the listed rules.
        "PF-09" => {
            let lean = lean_of(&two_theorems(
                "For every natural number \\(m\\), \\(m + 0 = m\\).",
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{simplify}{goal}\n\\rule{\\reference{Main::first}}\n\\end{simplify}\nClose the goal by reflexivity.",
            ));
            assert!(
                lean.contains("simp only ["),
                "simplify is simp only: {lean}"
            );
            // No rule list at all is unrestricted simplification: rejected.
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{simplify}{goal}\n\\end{simplify}",
                ),
                &["LLF5003"],
            );
        }
        // §16.7: constructor with the exact ordered branch count.
        "PF-10" => {
            let module = theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\) and \\(n * 1 = n\\).",
                "\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\begin{branch}{2}\nClose the goal by reflexivity.\n\\end{branch}\n\\end{constructor}",
            );
            let lean = lean_of(&module);
            assert!(lean.contains("constructor"), "the pinned lowering: {lean}");
            fails_within(
                &module.replacen(
                    "\\begin{branch}{2}\nClose the goal by reflexivity.\n\\end{branch}\n",
                    "",
                    1,
                ),
                &["LLF5003", "LLF5004"],
            );
        }
        // §16.8: cases needs the descriptor, every constructor, exact binders.
        "PF-11" => {
            let module = theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{cases}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n\\end{cases}",
            );
            let lean = lean_of(&module);
            assert!(
                lean.contains("cases") && lean.contains("| zero") && lean.contains("| succ"),
                "the pinned cases lowering: {lean}"
            );
            fails_within(
                &module.replacen(
                    "\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n",
                    "",
                    1,
                ),
                &["LLF5003"],
            );
            fails_within(
                &module.replacen("\\bind{m}", "\\bind{m;extra}", 1),
                &["LLF5003"],
            );
        }
        // §16.9: induction with exact field and IH binders.
        "PF-12" => {
            let module = theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{induction}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m;ih}\nClose the goal by reflexivity.\n\\end{case}\n\\end{induction}",
            );
            let lean = lean_of(&module);
            assert!(
                lean.contains("induction") && lean.contains("| succ"),
                "the pinned induction lowering: {lean}"
            );
            fails_within(
                &module.replacen("\\bind{m;ih}", "\\bind{m}", 1),
                &["LLF5003"],
            );
        }
        // §16.10: one declared relation, one or more steps, exact endpoints.
        "PF-13" => {
            let module = two_theorems(
                "\\(0 + 0 = 0\\).",
                "\\(0 + 0 = 0\\).",
                "\\begin{calculate}\n\\start{0 + 0}\n\\step{lexlean.core::eq}{0}{\\reference{Main::first}}\n\\end{calculate}",
            );
            let lean = lean_of(&module);
            assert!(lean.contains("calc"), "the pinned calc lowering: {lean}");
            fails_within(
                &module.replacen(
                    "\\step{lexlean.core::eq}{0}{\\reference{Main::first}}\n",
                    "",
                    1,
                ),
                &["LLF5003"],
            );
        }
        // §16.1: no capture or leak across branch and premise scopes.
        "PF-14" => {
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{cases}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n\\end{cases}\nClose the goal with \\(m\\).",
                ),
                &["LLF5002", "LLP2002", "LLL1004", "LLT4001"],
            );
        }
        // §16.12: every goal closes; nothing follows closure.
        "PF-15" => {
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), if \\(n = n\\), then \\(n + 0 = n\\).",
                    "Assume \\(h\\).",
                ),
                &["LLF5004"],
            );
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Close the goal by reflexivity.\nClose the goal by reflexivity.",
                ),
                &["LLF5002"],
            );
        }
        // §16.12: no raw tactics, custom nodes, automation, or holes.
        "PF-16" => {
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "By simp.",
                ),
                &["LLF5005", "LLL1004"],
            );
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "The proof is omitted.",
                ),
                &["LLF5005", "LLL1004"],
            );
        }
        // §16.12: native_decide is never accepted or generated.
        "PF-17" => {
            fails_within(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Close the goal by native_decide.",
                ),
                &["LLF5005", "LLL1004"],
            );
            let semantics = std::fs::read_to_string(
                support::repo_root()
                    .join("language/semantics.toml")
                    .as_std_path(),
            )
            .expect("semantics");
            assert!(
                !semantics.contains("native_decide"),
                "no semantic constructor names native_decide"
            );
            let lean = support::lean_text(&support::rendered(&P::example()), "Main");
            assert!(!lean.contains("native_decide"), "never generated");
        }
        // §20.4: Lean proof failures remap to the source proof span.
        "PF-18" => {
            let (project, error) = support::broken_proof();
            support::expect_code(error, "LLV7002");
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLV7002")
                .expect("matched");
            let span = diagnostic
                .primary
                .as_ref()
                .expect("a remapped Lean failure has a source span");
            assert!(
                span.path.ends_with("Main.lex.tex"),
                "the failure remaps into the source module, found {}",
                span.path
            );
            let source = project.read("src/Main.lex.tex");
            let covered = &source[span.byte_start..span.byte_end.min(source.len())];
            assert!(
                source.contains("reflexivity") && !covered.is_empty(),
                "the span covers originating source text, found {covered:?}"
            );
        }
        other => panic!("no proofs case is wired for {other}"),
    }
}
