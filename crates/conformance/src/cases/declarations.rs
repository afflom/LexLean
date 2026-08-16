//! The `declarations` suite: DF-01..DF-10.

use lexlean::ir::declaration::{DeclBody, DeclKind};

use crate::support::{self, P};

pub(crate) fn run(id: &str) {
    match id {
        // §15.7 rule 9: one nonrecursive sort-valued def, entry-linked; an
        // ambiguous type phrase is rejected, and formatting retains the
        // qualified selector that disambiguates (C7, D2).
        "DF-01" => {
            let project = support::defs_project();
            project.check_ok();
            let lean = support::lean_text(&support::rendered(&project), "Main");
            assert!(
                lean.contains("public def count : Type :=\n  Nat\n"),
                "a type definition is a sort-valued def: {lean}"
            );
            let ambiguous = support::defs_project();
            ambiguous.add_package(
                "lexicons/test-dupnat",
                "test.dupnat",
                &["lexlean.core@1.0.0"],
                &[("nat2.toml", DUP_NAT_ENTRY)],
            );
            ambiguous.edit(
                "src/Main.lex.tex",
                "\\useglossary{test.defs@1.0.0}",
                "\\useglossary{test.defs@1.0.0}\n\\useglossary{test.dupnat@1.0.0}",
            );
            ambiguous.edit(
                "src/Main.lex.tex",
                "A count is defined as \\(ℕ\\).",
                "A count is defined as natural number.",
            );
            ambiguous.relock();
            let error = ambiguous.check_fails_with("LLP2002");
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLP2002")
                .expect("matched");
            assert!(
                diagnostic.message.contains("lexlean.std.nat::nat")
                    && diagnostic.message.contains("test.dupnat::nat2"),
                "the definition ambiguity names both candidates: {}",
                diagnostic.message
            );
            // With explicit selectors the module checks, and canonical
            // formatting keeps every selector the bare surface would not
            // resolve uniquely.
            ambiguous.write(
                "src/Main.lex.tex",
                &support::DEFS_MODULE
                    .replace(
                        "\\useglossary{test.defs@1.0.0}",
                        "\\useglossary{test.defs@1.0.0}\n\\useglossary{test.dupnat@1.0.0}",
                    )
                    .replace(
                        "A count is defined as \\(ℕ\\).",
                        "A count is defined as \\(\\lexeme{lexlean.std.nat::nat}\\).",
                    )
                    .replace(
                        "natural number \\(",
                        "\\(\\lexeme{lexlean.std.nat::nat}\\) \\(",
                    ),
            );
            let checked = support::checked_project(&ambiguous);
            let canonical =
                lexlean::fmt::canonical_source(&checked.modules["Main"], &checked.closure)
                    .expect("formats");
            assert!(
                canonical.contains("A count is defined as \\(\\lexeme{lexlean.std.nat::nat}\\).")
                    && canonical.contains("For every \\(\\lexeme{lexlean.std.nat::nat}\\) \\(n\\), \\(double(n)\\) is defined as \\(n + n\\)."),
                "formatting retains the disambiguating selectors: {canonical}"
            );
            ambiguous.write("src/Main.lex.tex", &canonical);
            ambiguous.check_ok();
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
        // §15.7: an explicitly typed nonrecursive term def, through a call
        // self head or a noun-of self head, with `;`-separated binders,
        // Lean-verified in the corpus and reproduced by the formatter.
        "DF-02" => {
            let project = support::defs_project();
            let lean = support::lean_text(&support::rendered(&project), "Main");
            assert!(
                lean.contains("public def double (llv0 : Nat) : Nat :=\n  Nat.add llv0 llv0\n"),
                "the term definition emits an explicitly typed def: {lean}"
            );
            let fixture = support::verified_corpus();
            assert_eq!(fixture.attestation["status"], "verified");
            assert_eq!(
                support::corpus_declaration_lean("double"),
                "public def double (llv0 : Nat) : Nat :=\n  Nat.add llv0 llv0"
            );
            assert_eq!(
                support::corpus_declaration_lean("combine"),
                "public def combine (llv0 : Nat) (llv1 : Nat) : Nat :=\n  Nat.add llv0 llv1"
            );
            let checked = support::checked_project(&fixture.project);
            let canonical =
                lexlean::fmt::canonical_source(&checked.modules["Main"], &checked.closure)
                    .expect("formats");
            assert!(
                canonical.contains("For every natural number \\(n\\), the double of \\(n\\) is defined as \\(n + n\\).")
                    && canonical.contains("For every natural number \\(a\\); natural number \\(b\\), \\(combine(a, b)\\) is defined as \\(a + b\\).")
                    && canonical.contains("For every natural number \\(n\\), the double of \\(n\\) is even."),
                "noun-of self heads, `;` binder lists, and noun-of arguments format canonically: {canonical}"
            );
            // The canonical source of the whole corpus is itself a valid,
            // canonical module (§23.5).
            let reformatted = support::corpus_project();
            reformatted.write("src/Main.lex.tex", &canonical);
            reformatted.check_ok();
            let again = support::checked_project(&reformatted);
            assert_eq!(
                lexlean::fmt::canonical_source(&again.modules["Main"], &again.closure)
                    .expect("formats"),
                canonical,
                "canonical formatting is idempotent over the corpus"
            );
            // `and` between definition binders is not the §15.4 BINDER-LIST
            // separator; a noun-of head with the wrong argument fails rule 4.
            let anded = support::corpus_project();
            anded.edit(
                "src/Main.lex.tex",
                "natural number \\(a\\); natural number \\(b\\), \\(combine(a, b)\\)",
                "natural number \\(a\\) and natural number \\(b\\), \\(combine(a, b)\\)",
            );
            anded.check_fails_with("LLF5001");
            let wrong = support::corpus_project();
            wrong.edit(
                "src/Main.lex.tex",
                "the double of \\(n\\) is defined as",
                "the double of \\(m\\) is defined as",
            );
            let error = wrong.check_fails_with("LLF5001");
            assert!(
                error.diagnostics.iter().all(|d| d.primary.is_some()),
                "self-head diagnostics carry spans: {error}"
            );
        }
        // §15.7 rule 10: a Prop-valued predicate def, through a constant
        // or a text predicate-frame self head (S10), Lean-verified.
        "DF-03" => {
            let project = support::defs_project();
            let lean = support::lean_text(&support::rendered(&project), "Main");
            assert!(
                lean.contains("public def good : Prop :=\n  Exists (fun llv0 => Eq llv0 llv0)\n"),
                "a predicate def returns Prop: {lean}"
            );
            let fixture = support::verified_corpus();
            assert_eq!(fixture.attestation["status"], "verified");
            assert_eq!(
                support::corpus_declaration_lean("even"),
                "public def even (llv0 : Nat) : Prop :=\n  Exists (fun llv1 => Eq llv0 (Nat.add llv1 llv1))"
            );
            assert_eq!(
                support::corpus_declaration_lean("double_even"),
                "public theorem double_even (llv0 : Nat) : LexLeanExample.Main.even (LexLeanExample.Main.double llv0) := by\n  refine ⟨llv0, ?_⟩\n  rfl"
            );
            let checked = support::checked_project(&fixture.project);
            let canonical =
                lexlean::fmt::canonical_source(&checked.modules["Main"], &checked.closure)
                    .expect("formats");
            assert!(
                canonical.contains("For every natural number \\(n\\), \\(n\\) is even holds exactly when there exists a natural number \\(k\\) such that \\(n = k + k\\)."),
                "the predicate-frame self head formats canonically: {canonical}"
            );
            // The self head must be the frame over the declared binder.
            let wrong = support::corpus_project();
            wrong.edit(
                "src/Main.lex.tex",
                "\\(n\\) is even holds exactly when",
                "\\(k\\) is even holds exactly when",
            );
            let error = wrong.check_fails_with("LLF5001");
            assert!(
                error.diagnostics.iter().all(|d| d.primary.is_some()),
                "self-head diagnostics carry spans: {error}"
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
            // Rule 4 holds without a `For every` prefix: a function entry
            // defined as a constant declares too few binders (C16).
            let constant = support::defs_project();
            constant.edit(
                "src/Main.lex.tex",
                "For every natural number \\(n\\), \\(double(n)\\) is defined as \\(n + n\\).",
                "\\(double\\) is defined as \\(0\\).",
            );
            constant.check_fails_with("LLT4004");
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

/// A second type-noun with the text surface `natural number` and the math
/// surface `ℕ`, so bare surfaces resolve to two visible entries.
const DUP_NAT_ENTRY: &str = r#"spec = "lexlean/entry/1"
id = "nat2"
category = "type-noun"
signature = "(sort (type 0))"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Int"

[[form]]
id = "natural-number"
channel = "text"
surface = "natural number"
canonical_source = true
features = ["article-a", "lower-case", "singular"]

[[form]]
id = "blackboard"
channel = "math"
surface = "ℕ"
canonical_source = true
features = []

[render]
math = "(seq (token mathbb) (group (token blackboard-n)))"
"#;
