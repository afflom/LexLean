//! The `proofs` suite: PF-01..PF-18.
//!
//! Positive forms are asserted against the shared Lean-verified proof
//! corpus (`support::verified_corpus`): every case first asserts the
//! corpus attestation succeeded, then the exact generated Lean of the
//! declaration exercising its form. Negative forms assert exact diagnostic
//! codes on single-theorem modules.

use crate::support::{self, P};

/// The full generated Lean name prefix of the corpus module.
const M: &str = "LexLeanExample.Main";

/// A one-theorem module with the given statement and proof body.
fn theorem_module(statement: &str, proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{main-goal}}\n\\noaxioms\n{statement}\n\\begin{{proof}}\n{proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

/// A two-theorem module: `helper` (proved by reflexivity) then `second`.
fn two_theorems(first_statement: &str, second_statement: &str, second_proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{helper}}\n\\noaxioms\n{first_statement}\n\\begin{{proof}}\nClose the goal by reflexivity.\n\\end{{proof}}\n\\end{{theorem}}\n\n\\begin{{theorem}}{{second}}\n\\noaxioms\n{second_statement}\n\\begin{{proof}}\n{second_proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

/// Two theorems where `helper` is a conditional proved by Assume, so its
/// application yields statically determined residual premises.
fn conditional_lemma_pair(
    first_statement: &str,
    second_statement: &str,
    second_proof: &str,
) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{helper}}\n\\noaxioms\n{first_statement}\n\\begin{{proof}}\nAssume \\(h\\).\nClose the goal by reflexivity.\n\\end{{proof}}\n\\end{{theorem}}\n\n\\begin{{theorem}}{{second}}\n\\noaxioms\n{second_statement}\n\\begin{{proof}}\n{second_proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

fn project_with(module: &str) -> P {
    let project = P::example();
    project.write("src/Main.lex.tex", module);
    project
}

/// Check a module, expecting exactly the given failure code, and return the
/// matching diagnostic.
fn fails_with(module: &str, code: &str) -> lexlean::diagnostic::Diagnostic {
    let error = project_with(module).check_err();
    support::expect_code(&error, code);
    error
        .diagnostics
        .into_iter()
        .find(|d| d.code.as_str() == code)
        .expect("matched")
}

/// Assert that one corpus declaration's generated Lean is exactly `expected`,
/// and — where the pinned toolchain is installed — that the corpus verified.
///
/// The generated Lean is a `build` product and is asserted on every supported
/// host; only the attestation needs Lean (§8.3).
fn corpus_exact(id: &str, lean_name: &str, expected: &str) {
    if let Some(fixture) = support::corpus_backed(id) {
        assert_eq!(
            fixture.attestation["status"], "verified",
            "the corpus attestation records success"
        );
    }
    assert_eq!(
        support::corpus_declaration_lean(lean_name),
        expected,
        "exact generated Lean for `{lean_name}`"
    );
}

pub(crate) fn run(id: &str) {
    match id {
        // §16.2: Assume introduces scoped locals (`intro`); Close-with is
        // `exact`; both Lean-verified in the corpus.
        "PF-01" => {
            corpus_exact("PF-01", 
                "rewrite_hypothesis",
                &format!("public theorem rewrite_hypothesis (llv0 : Nat) : (Eq (Nat.add llv0 0) (1 : Nat)) → Eq llv0 (1 : Nat) := by\n  intro llh0\n  rw [{M}.add_zero] at llh0\n  exact llh0"),
            );
            corpus_exact("PF-01", 
                "init_zero_add",
                "public theorem init_zero_add (llv0 : Nat) : Eq (Nat.add 0 llv0) llv0 := by\n  exact Nat.zero_add llv0",
            );
            // A leading universal binder is already a parameter: Assume of
            // it is diagnosed by name (S6).
            let diagnostic = fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Assume \\(n\\).\nClose the goal by reflexivity.",
                ),
                "LLF5002",
            );
            assert!(
                diagnostic
                    .message
                    .contains("already a declaration parameter"),
                "the lifted-binder Assume names the cause: {}",
                diagnostic.message
            );
            assert!(
                diagnostic.primary.is_some(),
                "the diagnostic carries a span"
            );
            // Assume on a known conjunction goal is a shape error.
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\) and \\(n = n\\).",
                    "Assume \\(h\\).\nClose the goal by reflexivity.",
                ),
                "LLF5002",
            );
            // `Not P` is `P → False` (§16.2): a hypothesis of the function
            // type closes the negation goal; the shapes are never certainly
            // distinct, and pinned Lean accepts the exact term.
            support::f1_exact("PF-01", 
                "not_intro",
                "public theorem not_intro (llv0 : Prop) : (llv0 → False) → Not llv0 := by\n  intro llh0\n  exact llh0",
            );
            // A certain shape mismatch stays rejected before Lean: an
            // equation hypothesis against a conjunction goal.
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), if \\(n = n\\), then \\(n = n\\) and \\(n = n\\).",
                    "Assume \\(h\\).\nClose the goal with \\(h\\).",
                ),
                "LLT4001",
            );
        }
        // §16.2: simple Apply needs exactly one residual premise; a
        // quantified lemma's conclusion unifies with the goal (C5).
        "PF-02" => {
            corpus_exact("PF-02", 
                "apply_known",
                &format!("public theorem apply_known (llv0 : Nat) : Eq (Nat.succ (Nat.add 0 llv0)) (Nat.succ llv0) := by\n  apply {M}.succ_congr\n  exact {M}.zero_add llv0"),
            );
            let diagnostic = fails_with(
                &conditional_lemma_pair(
                    "If \\(0 + 0 = 0\\), then if \\(0 * 0 = 0\\), then \\(0 - 0 = 0\\).",
                    "\\(0 - 0 = 0\\).",
                    "Apply \\(\\reference{Main::helper}\\).\nClose the goal by reflexivity.",
                )
                .replace("Assume \\(h\\).", "Assume \\(h\\).\nAssume \\(g\\)."),
                "LLF5002",
            );
            assert!(
                diagnostic.message.contains("yields 2"),
                "the residual count is named: {}",
                diagnostic.message
            );
            // An external predicate (`Ne`) may reduce to a function type in
            // Lean: its residual is unknown, not zero, and Lean's `apply`
            // decides (§16.1).
            support::f1_exact("PF-02", 
                "apply_ne",
                "public theorem apply_ne (llv0 : Nat) : (Ne (Nat.succ llv0) 0) → (Eq (Nat.succ llv0) (0 : Nat)) → False := by\n  intro llh0\n  intro llh1\n  apply llh0\n  exact llh1",
            );
        }
        // §16.6: structured apply names every premise once, in order.
        "PF-03" => {
            corpus_exact("PF-03", 
                "structured_apply",
                &format!("public theorem structured_apply (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  apply {M}.two_premises\n  rfl\n  exact Nat.zero_add llv0"),
            );
            let module = conditional_lemma_pair(
                "If \\(0 + 0 = 0\\), then if \\(0 * 0 = 0\\), then \\(0 - 0 = 0\\).",
                "\\(0 - 0 = 0\\).",
                "\\begin{apply}{\\reference{Main::helper}}\n\\begin{premise}{1}\nClose the goal by reflexivity.\n\\end{premise}\n\\begin{premise}{2}\nClose the goal by reflexivity.\n\\end{premise}\n\\end{apply}",
            )
            .replace(
                "Assume \\(h\\).",
                "Assume \\(h\\).\nAssume \\(g\\).",
            );
            project_with(&module).check_ok();
            fails_with(
                &module.replacen("{premise}{1}", "{premise}{2}", 1),
                "LLF5003",
            );
            fails_with(
                &module.replacen(
                    "\\begin{premise}{2}\nClose the goal by reflexivity.\n\\end{premise}\n",
                    "",
                    1,
                ),
                "LLF5003",
            );
        }
        // §16.2: Reflexivity is exactly pinned rfl and closes the goal.
        "PF-04" => {
            corpus_exact(
                "PF-04",
                "add_zero",
                "public theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  rfl",
            );
            let diagnostic = fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Close the goal by reflexivity.\nClose the goal by reflexivity.",
                ),
                "LLF5002",
            );
            assert!(
                diagnostic.primary.is_some(),
                "the closed-branch step has a span"
            );
            // Reflexivity on a known conjunction goal is a shape error.
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\) and \\(n = n\\).",
                    "Close the goal by reflexivity.",
                ),
                "LLF5002",
            );
        }
        // §16.2: witness supplies the next existential witness only; a
        // unique-existence witness leaves the And residual (C4).
        "PF-05" => {
            corpus_exact("PF-05", 
                "exists_witness",
                "public theorem exists_witness : Exists (fun (llv0 : Nat) => Eq (Nat.add llv0 0) (0 : Nat)) := by\n  refine ⟨(0 : Nat), ?_⟩\n  rfl",
            );
            corpus_exact("PF-05", 
                "exists_unique",
                "public theorem exists_unique : Exists (fun (llv0 : Nat) => And (Eq llv0 (0 : Nat)) ((llv1 : Nat) → (Eq llv1 (0 : Nat)) → Eq llv1 llv0)) := by\n  refine ⟨(0 : Nat), ?_⟩\n  constructor\n  rfl\n  intro _llh0 llh1\n  exact llh1",
            );
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Use \\(0\\) as the witness.\nClose the goal by reflexivity.",
                ),
                "LLF5002",
            );
            // The unique-existence residual is exactly the conjunction: a
            // one-branch constructor is rejected before Lean.
            fails_with(
                &theorem_module(
                    "There exists exactly one natural number \\(k\\) such that \\(k = 0\\).",
                    "Use \\(0\\) as the witness.\n\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\end{constructor}",
                ),
                "LLF5003",
            );
        }
        // §16.2: Left/Right select the disjunction constructor, including
        // inside case branches (S3).
        "PF-06" => {
            corpus_exact("PF-06", 
                "select_right",
                "public theorem select_right (llv0 : Nat) : Or (Eq llv0 (1 : Nat)) (Eq (Nat.add llv0 0) llv0) := by\n  right\n  rfl",
            );
            corpus_exact("PF-06", 
                "cases_nat",
                "public theorem cases_nat (llv0 : Nat) : Or (Eq (Nat.add llv0 0) llv0) (Eq llv0 (1 : Nat)) := by\n  cases llv0 with\n    | zero =>\n      left\n      rfl\n    | succ _llh0 =>\n      left\n      rfl",
            );
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Select the left alternative.\nClose the goal by reflexivity.",
                ),
                "LLF5002",
            );
        }
        // §16.3: have establishes, then scopes the fresh hypothesis.
        "PF-07" => {
            corpus_exact("PF-07", 
                "have_step",
                &format!("public theorem have_step (llv0 : Nat) : Eq (Nat.add 0 llv0) (Nat.add llv0 0) := by\n  have llh0 : Eq (Nat.add 0 llv0) llv0 := by\n    exact Nat.zero_add llv0\n  rw [llh0, {M}.add_zero]"),
            );
            // The hypothesis does not leak backward: using it before the
            // have fails.
            let error = project_with(&theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "Close the goal with \\(h\\).",
            ))
            .check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLL1004" | "LLT4001")),
                "an unknown hypothesis spelling has no reading: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
            // The reserved target word and non-identifier spellings are not
            // hypothesis names (C15).
            for name in ["goal", "h.1", "1h"] {
                fails_with(
                    &theorem_module(
                        "For every natural number \\(n\\), \\(n + 0 = n\\).",
                        &format!("\\begin{{have}}{{{name}}}\n\\(n + 0 = n\\).\n\\begin{{proof}}\nClose the goal by reflexivity.\n\\end{{proof}}\n\\end{{have}}\nClose the goal by reflexivity."),
                    ),
                    "LLF5002",
                );
            }
        }
        // §16.4: every rule, in source order, directed, at one target; a
        // rewrite that closes the goal by rfl ends the proof (S8).
        "PF-08" => {
            corpus_exact("PF-08", 
                "succ_congr",
                "public theorem succ_congr (llv0 : Nat) (llv1 : Nat) : (Eq llv0 llv1) → Eq (Nat.succ llv0) (Nat.succ llv1) := by\n  intro llh0\n  rw [llh0]",
            );
            corpus_exact("PF-08", 
                "rewrite_backward",
                &format!("public theorem rewrite_backward (llv0 : Nat) (llv1 : Nat) : Eq (Nat.succ (Nat.add llv0 llv1)) (Nat.add llv0 (Nat.succ llv1)) := by\n  rw [← {M}.add_succ]"),
            );
            corpus_exact("PF-08", 
                "implies_rewrite",
                &format!("public theorem implies_rewrite (llv0 : Nat) : (Eq llv0 (1 : Nat)) → Eq (Nat.add llv0 0) (1 : Nat) := by\n  intro llh0\n  rw [{M}.add_zero]\n  exact llh0"),
            );
            // A non-equation rule is rejected.
            fails_with(
                &two_theorems(
                    "For every natural number \\(m\\), \\(m + 0 = m\\) or \\(m = 1\\).",
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{rewrite}{goal}\n\\forward{\\reference{Main::helper}}\n\\end{rewrite}\nClose the goal by reflexivity.",
                ),
                "LLF5002",
            );
            // A data binder is not a rewrite target (C19).
            fails_with(
                &two_theorems(
                    "For every natural number \\(m\\), \\(m + 0 = m\\).",
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{rewrite}{n}\n\\forward{\\reference{Main::helper}}\n\\end{rewrite}\nClose the goal by reflexivity.",
                ),
                "LLF5002",
            );
        }
        // §16.5: simplify is simp only with exactly the listed rules; a
        // simp that closes the goal ends the proof (S8).
        "PF-09" => {
            corpus_exact("PF-09", 
                "simplify_both",
                &format!("public theorem simplify_both (llv0 : Nat) : (Eq (Nat.add 0 llv0) (1 : Nat)) → Eq (Nat.add llv0 0) (1 : Nat) := by\n  intro llh0\n  simp only [{M}.zero_add] at llh0\n  simp only [{M}.add_zero]\n  exact llh0"),
            );
            corpus_exact("PF-09", 
                "simplify_closes",
                &format!("public theorem simplify_closes (llv0 : Nat) : (Eq llv0 (1 : Nat)) → Eq (Nat.add llv0 0) (1 : Nat) := by\n  intro llh0\n  simp only [{M}.add_zero, llh0]"),
            );
            // No rule list at all is unrestricted simplification: rejected.
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{simplify}{goal}\n\\end{simplify}",
                ),
                "LLF5003",
            );
            // A data term is not a simp rule (C19).
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{simplify}{goal}\n\\rule{n}\n\\end{simplify}",
                ),
                "LLF5002",
            );
        }
        // §16.7: constructor with the exact ordered branch count, over And,
        // Iff, and a glossary-declared structure (C13).
        "PF-10" => {
            corpus_exact("PF-10", 
                "constructor_and",
                "public theorem constructor_and (llv0 : Nat) : And (Eq (Nat.add llv0 0) llv0) (Eq (Nat.add 0 llv0) llv0) := by\n  constructor\n  rfl\n  exact Nat.zero_add llv0",
            );
            corpus_exact("PF-10", 
                "constructor_iff",
                "public theorem constructor_iff (llv0 : Nat) : Iff (Eq (Nat.add llv0 0) llv0) (Eq llv0 llv0) := by\n  constructor\n  intro _llh0\n  rfl\n  intro _llh1\n  rfl",
            );
            corpus_exact("PF-10", 
                "constructor_structure",
                "public theorem constructor_structure (llv0 : Nat) : And (Eq (Nat.add llv0 0) llv0) (Eq (Nat.add 0 llv0) llv0) := by\n  constructor\n  rfl\n  exact Nat.zero_add llv0",
            );
            let module = theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\) and \\(n * 1 = n\\).",
                "\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\begin{branch}{2}\nClose the goal by reflexivity.\n\\end{branch}\n\\end{constructor}",
            );
            project_with(&module).check_ok();
            fails_with(
                &module.replacen(
                    "\\begin{branch}{2}\nClose the goal by reflexivity.\n\\end{branch}\n",
                    "",
                    1,
                ),
                "LLF5003",
            );
            // A disjunction is not a constructor target.
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\) or \\(n = 1\\).",
                    "\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\end{constructor}",
                ),
                "LLF5002",
            );
        }
        // §16.8: cases needs the descriptor, every constructor, exact
        // binders; a hypothesis scrutinee binds typed fields.
        "PF-11" => {
            corpus_exact("PF-11", 
                "or_comm",
                "public theorem or_comm (llv0 : Nat) : (Or (Eq llv0 (0 : Nat)) (Eq llv0 (1 : Nat))) → Or (Eq llv0 (1 : Nat)) (Eq llv0 (0 : Nat)) := by\n  intro llh0\n  cases llh0 with\n    | inl llh1 =>\n      right\n      exact llh1\n    | inr llh2 =>\n      left\n      exact llh2",
            );
            corpus_exact("PF-11", 
                "and_comm",
                "public theorem and_comm (llv0 : Nat) : (And (Eq llv0 (0 : Nat)) (Eq (Nat.add llv0 0) llv0)) → And (Eq (Nat.add llv0 0) llv0) (Eq llv0 (0 : Nat)) := by\n  intro llh0\n  cases llh0 with\n    | intro llh1 llh2 =>\n      constructor\n      exact llh2\n      exact llh1",
            );
            corpus_exact("PF-11", 
                "not_both",
                "public theorem not_both (llv0 : Nat) : Not (And (Eq llv0 llv0) (Not (Eq llv0 llv0))) := by\n  intro llh0\n  cases llh0 with\n    | intro llh1 llh2 =>\n      apply llh2\n      exact llh1",
            );
            let module = theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{cases}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n\\end{cases}",
            );
            project_with(&module).check_ok();
            fails_with(
                &module.replacen(
                    "\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n",
                    "",
                    1,
                ),
                "LLF5003",
            );
            fails_with(
                &module.replacen("\\bind{m}", "\\bind{m;extra}", 1),
                "LLF5003",
            );
            // The branch goal is the constructor-specialized goal: a wrong
            // witness type in a branch is caught before Lean.
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{cases}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nSelect the left alternative.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n\\end{cases}",
                ),
                "LLF5002",
            );
        }
        // §16.9: induction with exact field and IH binders; the hypothesis
        // is typed by the goal at the field and usable via Close-with.
        "PF-12" => {
            corpus_exact("PF-12", 
                "zero_add",
                &format!("public theorem zero_add (llv0 : Nat) : Eq (Nat.add 0 llv0) llv0 := by\n  induction llv0 with\n    | zero =>\n      rfl\n    | succ _llh0 llh1 =>\n      rw [{M}.add_succ]\n      apply {M}.succ_congr\n      exact llh1"),
            );
            let module = theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{induction}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m;ih}\nClose the goal by reflexivity.\n\\end{case}\n\\end{induction}",
            );
            project_with(&module).check_ok();
            fails_with(&module.replacen("\\bind{m;ih}", "\\bind{m}", 1), "LLF5003");
        }
        // §16.10: one declared relation, two or more steps, exact endpoints
        // (free locals never conflate, C6).
        "PF-13" => {
            corpus_exact("PF-13", 
                "calculation",
                &format!("public theorem calculation (llv0 : Nat) : Eq (Nat.add 0 (Nat.add llv0 0)) llv0 := by\n  calc (Nat.add 0 (Nat.add llv0 0)) = (Nat.add llv0 0) := ({M}.zero_add (Nat.add llv0 0))\n    _ = llv0 := ({M}.add_zero llv0)"),
            );
            let module = two_theorems(
                "\\(0 + 0 = 0\\).",
                "\\(0 + 0 = 0\\).",
                "\\begin{calculate}\n\\start{0 + 0}\n\\step{lexlean.core::eq}{0}{\\reference{Main::helper}}\n\\end{calculate}",
            );
            project_with(&module).check_ok();
            fails_with(
                &module.replacen(
                    "\\step{lexlean.core::eq}{0}{\\reference{Main::helper}}\n",
                    "",
                    1,
                ),
                "LLF5003",
            );
            // A distinct free local at an endpoint is a mismatch, not an
            // alpha-equivalent term.
            fails_with(
                &two_theorems(
                    "For every natural number \\(m\\), \\(m + 0 = m\\).",
                    "For every natural number \\(n\\) and natural number \\(m\\), \\(n + 0 = n\\).",
                    "\\begin{calculate}\n\\start{m + 0}\n\\step{lexlean.core::eq}{n}{\\reference{Main::helper}(n)}\n\\end{calculate}",
                ),
                "LLF5002",
            );
            // Endpoints match through definition unfolding (§16.10): the goal
            // spells `double(n) + 0`, the chain starts at `n + n + 0`; Lean's
            // `calc` accepts the same relation.
            support::f1_exact("PF-13", 
                "double_calc",
                "public theorem double_calc (llv0 : Nat) : Eq (Nat.add (LexLeanExample.Main.double llv0) 0) (Nat.add llv0 llv0) := by\n  calc (Nat.add (Nat.add llv0 llv0) 0) = (Nat.add llv0 llv0) := (LexLeanExample.Main.add_zero (Nat.add llv0 llv0))",
            );
        }
        // §16.1: no capture or leak across branch and premise scopes.
        "PF-14" => {
            let error = project_with(&theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{cases}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m}\nClose the goal by reflexivity.\n\\end{case}\n\\end{cases}\nClose the goal with \\(m\\).",
            ))
            .check_err();
            // The step after the closing cases is rejected first (§16.12).
            assert_eq!(
                error.diagnostics.first().map(|d| d.code.as_str()),
                Some("LLF5002"),
                "the branch local does not leak and the extra step is rejected: {error}"
            );
            // A premise-scoped hypothesis is invisible to a sibling premise.
            fails_with(
                &conditional_lemma_pair(
                    "If \\(0 + 0 = 0\\), then if \\(0 * 0 = 0\\), then \\(0 - 0 = 0\\).",
                    "\\(0 - 0 = 0\\).",
                    "\\begin{apply}{\\reference{Main::helper}}\n\\begin{premise}{1}\n\\begin{have}{k}\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{have}\nClose the goal with \\(k\\).\n\\end{premise}\n\\begin{premise}{2}\nClose the goal with \\(k\\).\n\\end{premise}\n\\end{apply}",
                )
                .replace("Assume \\(h\\).", "Assume \\(h\\).\nAssume \\(g\\)."),
                "LLL1004",
            );
        }
        // §16.12: every goal closes; nothing follows closure; a rewrite that
        // may close the goal ends the proof.
        "PF-15" => {
            let diagnostic = fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), if \\(n = n\\), then \\(n + 0 = n\\).",
                    "Assume \\(h\\).",
                ),
                "LLF5004",
            );
            assert!(
                diagnostic.primary.is_some(),
                "the open-goal diagnostic has a span"
            );
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Close the goal by reflexivity.\nClose the goal by reflexivity.",
                ),
                "LLF5002",
            );
            corpus_exact("PF-15", 
                "rewrite_backward",
                &format!("public theorem rewrite_backward (llv0 : Nat) (llv1 : Nat) : Eq (Nat.succ (Nat.add llv0 llv1)) (Nat.add llv0 (Nat.succ llv1)) := by\n  rw [← {M}.add_succ]"),
            );
        }
        // §16.12: no raw tactics, custom nodes, automation, or holes; each is
        // a forbidden proof form by name.
        "PF-16" => {
            for (proof, word) in [
                ("By simp.", "simp"),
                ("Close the goal by sorry.", "sorry"),
                ("Close the goal by omega.", "omega"),
                ("Close the goal with \\(?_\\).", "?_"),
                ("Close the goal with \\(_\\).", "_"),
                ("Close the goal by exact?.", "exact?"),
                ("Close the goal by simp_all.", "simp_all"),
                ("all_goals rfl.", "all_goals"),
            ] {
                let diagnostic = fails_with(
                    &theorem_module("For every natural number \\(n\\), \\(n + 0 = n\\).", proof),
                    "LLF5005",
                );
                assert!(
                    diagnostic
                        .message
                        .contains(&format!("`{word}` is a forbidden proof form")),
                    "{proof:?} names `{word}`: {}",
                    diagnostic.message
                );
                assert!(
                    diagnostic.primary.is_some(),
                    "the forbidden form has a span"
                );
            }
            let diagnostic = fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "The proof is omitted.",
                ),
                "LLF5005",
            );
            assert!(
                diagnostic
                    .message
                    .contains("not a registered proof sentence"),
                "an unregistered sentence is a forbidden form: {}",
                diagnostic.message
            );
        }
        // §16.12: native_decide is never accepted or generated.
        "PF-17" => {
            let diagnostic = fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "Close the goal by native_decide.",
                ),
                "LLF5005",
            );
            assert!(
                diagnostic
                    .message
                    .contains("`native_decide` is a forbidden proof form"),
                "{}",
                diagnostic.message
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
            let lean = support::corpus_lean();
            assert!(!lean.contains("native_decide"), "never generated");
            assert!(!lean.contains("sorry"), "never generated");
        }
        // §20.4: Lean proof failures remap to the source proof span.
        "PF-18" => {
            if !support::lean_backed("PF-18") {
                return;
            }
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
