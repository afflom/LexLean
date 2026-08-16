//! The `declarations` suite: DF-01..DF-10.

use lexlean::ir::declaration::{DeclBody, DeclKind};

use crate::support::{self, P};

pub(crate) fn run(id: &str) {
    match id {
        // §15.7 rule 9: one nonrecursive sort-valued def, entry-linked.
        "DF-01" => {
            let project = support::defs_project();
            project.check_ok();
            let lean = support::lean_text(&support::rendered(&project), "Main");
            assert!(
                lean.contains("def count : Type :=\n  Nat"),
                "a type definition is a sort-valued def: {lean}"
            );
            let checked = support::checked_project(&project);
            let declaration = checked.modules["Main"]
                .document
                .declarations()
                .into_iter()
                .find(|d| d.component == "count")
                .expect("count exists");
            match &declaration.body {
                DeclBody::Definition { entry, .. } => {
                    assert_eq!(entry.to_string(), "test.defs::count", "linked to its entry");
                }
                DeclBody::TheoremLike { .. } => panic!("count is a definition"),
            }
        }
        // §15.7: an explicitly typed nonrecursive term def.
        "DF-02" => {
            let project = support::defs_project();
            let lean = support::lean_text(&support::rendered(&project), "Main");
            assert!(
                lean.contains("def double"),
                "the term definition emits a def: {lean}"
            );
            let line = lean
                .lines()
                .find(|line| line.contains("def double"))
                .expect("double's line");
            assert!(
                line.contains(": Nat :="),
                "the def carries its explicit result type: {line}"
            );
        }
        // §15.7 rule 10: a Prop-valued predicate def.
        "DF-03" => {
            let project = support::defs_project();
            let lean = support::lean_text(&support::rendered(&project), "Main");
            let line = lean
                .lines()
                .find(|line| line.contains("def good"))
                .expect("good's line");
            assert!(
                line.contains(": Prop :="),
                "a predicate def returns Prop: {line}"
            );
        }
        // §15.7 rules 6-8: no self reference, mutual cycle, or forward use.
        "DF-04" => {
            let recursive = support::defs_project();
            recursive.edit(
                "src/Main.lex.tex",
                "\\(double(n)\\) is defined as \\(n + n\\)",
                "\\(double(n)\\) is defined as \\(double(n) + n\\)",
            );
            let error = recursive.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLF5001" | "LLR3003" | "LLR3005")),
                "self recursion is rejected: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );

            let forward = support::defs_project();
            // Move `good` (which references nothing) before `count`, and make
            // it reference the later `double`.
            forward.edit(
                "src/Main.lex.tex",
                "\\(good\\) holds exactly when there exists a natural number \\(k\\) such that \\(k = k\\)",
                "\\(good\\) holds exactly when there exists a natural number \\(k\\) such that \\(double(k) = k\\)",
            );
            let text = forward.read("src/Main.lex.tex");
            let good_block_start = text
                .find("\\begin{predicatedefinition}")
                .expect("good block");
            let good_block_end = text.find("\\end{predicatedefinition}").expect("good end")
                + "\\end{predicatedefinition}".len();
            let good_block = text[good_block_start..good_block_end].to_owned();
            let without = format!(
                "{}{}",
                &text[..good_block_start],
                text[good_block_end..].trim_start_matches('\n')
            );
            let reordered = without.replace(
                "\\begin{typedefinition}",
                &format!("{good_block}\n\n\\begin{{typedefinition}}"),
            );
            forward.write("src/Main.lex.tex", &reordered);
            let error = forward.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLR3005" | "LLF5001")),
                "a forward reference is rejected: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §15.7 rule 4: the self application is exact and ordered.
        "DF-05" => {
            let doubled = support::defs_project();
            doubled.edit(
                "src/Main.lex.tex",
                "\\(double(n)\\) is defined as",
                "\\(double(n, n)\\) is defined as",
            );
            doubled.check_fails_with("LLF5001");

            let renamed = support::defs_project();
            renamed.edit(
                "src/Main.lex.tex",
                "For every natural number \\(n\\), \\(double(n)\\)",
                "For every natural number \\(n\\), \\(double(m)\\)",
            );
            renamed.check_fails_with("LLF5001");
        }
        // §15.9: exactly one explicit axiom policy everywhere.
        "DF-06" => {
            let missing = support::defs_project();
            missing.edit(
                "src/Main.lex.tex",
                "\\begin{typedefinition}{count}{test.defs::count}\n\\noaxioms\n",
                "\\begin{typedefinition}{count}{test.defs::count}\n",
            );
            missing.check_fails_with("LLP2003");

            let project = support::defs_project();
            let json = support::checked_project(&project)
                .linked
                .to_json()
                .to_canonical_string();
            assert!(
                json.contains("\"policy\""),
                "every linked declaration records its policy: {json}"
            );
        }
        // §15.8: theorem, lemma, corollary all emit Lean theorems while the
        // document metadata stays distinct.
        "DF-07" => {
            let project = P::example();
            project.edit(
                "src/Main.lex.tex",
                "\\begin{theorem}{add-zero}",
                "\\begin{lemma}{add-zero}",
            );
            project.edit("src/Main.lex.tex", "\\end{theorem}", "\\end{lemma}");
            project.check_ok();
            let build = support::rendered(&project);
            let lean = support::lean_text(&build, "Main");
            assert!(
                lean.contains("theorem add_zero"),
                "a lemma emits Lean theorem: {lean}"
            );
            let tex = support::tex_text(&build, "Main");
            assert!(
                tex.contains("\\begin{lemma}"),
                "the document keeps the lemma kind: {tex}"
            );
            let checked = support::checked_project(&project);
            let kind = checked.modules["Main"]
                .document
                .declarations()
                .into_iter()
                .find(|d| d.component == "add-zero")
                .expect("declared")
                .kind;
            assert_eq!(kind, DeclKind::Lemma, "IR metadata keeps the kind");
        }
        // §15.8, §16.12: no author axioms, opaque forms, or proofless
        // theorem-likes.
        "DF-08" => {
            let axiom_env = P::example();
            axiom_env.edit(
                "src/Main.lex.tex",
                "\\begin{theorem}{add-zero}",
                "\\begin{axiom}{add-zero}",
            );
            axiom_env.edit("src/Main.lex.tex", "\\end{theorem}", "\\end{axiom}");
            axiom_env.check_fails_with("LLL1004");

            let proofless = P::example();
            proofless.edit(
                "src/Main.lex.tex",
                "\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n",
                "",
            );
            proofless.check_fails_with("LLF5005");
        }
        // §15.8: exactly one nonempty structured proof.
        "DF-09" => {
            let empty = P::example();
            empty.edit(
                "src/Main.lex.tex",
                "\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}",
                "\\begin{proof}\n\\end{proof}",
            );
            let error = empty.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLF5004" | "LLF5003" | "LLF5005")),
                "an empty proof is rejected: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );

            let doubled = P::example();
            doubled.edit(
                "src/Main.lex.tex",
                "\\end{proof}\n\\end{theorem}",
                "\\end{proof}\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}",
            );
            doubled.check_fails_with("LLP2003");
        }
        // §15.7 rule 7, §17.5: source order is preserved everywhere.
        "DF-10" => {
            let project = support::defs_project();
            let lean = support::lean_text(&support::rendered(&project), "Main");
            let positions: Vec<usize> = ["def count", "def double", "def good", "theorem add_zero"]
                .iter()
                .map(|needle| {
                    lean.find(needle)
                        .unwrap_or_else(|| panic!("{needle} in {lean}"))
                })
                .collect();
            let mut sorted = positions.clone();
            sorted.sort_unstable();
            assert_eq!(
                positions, sorted,
                "generated declarations preserve source order"
            );
        }
        other => panic!("no declarations case is wired for {other}"),
    }
}
