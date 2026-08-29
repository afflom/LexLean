//! The `declarations` suite: DF-01..DF-11.

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
                lean.contains("@[expose] public def count : Type :=\n  Nat\n"),
                "a type definition is a sort-valued def: {lean}"
            );
            // The right-hand side is a sort read through defined type nouns
            // (§13.6): a constant whose type is the defined noun `type`.
            support::f1_exact(
                "DF-01",
                "alias",
                "@[expose] public def alias : Type :=\n  Nat",
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
                lean.contains(
                    "@[expose] public def double (llv0 : Nat) : Nat :=\n  Nat.add llv0 llv0\n"
                ),
                "the term definition emits an explicitly typed def: {lean}"
            );
            if let Some(fixture) = support::corpus_backed("DF-02") {
                assert_eq!(fixture.attestation["status"], "verified");
            }
            assert_eq!(
                support::corpus_declaration_lean("double"),
                "@[expose] public def double (llv0 : Nat) : Nat :=\n  Nat.add llv0 llv0"
            );
            assert_eq!(
                support::corpus_declaration_lean("combine"),
                "@[expose] public def combine (llv0 : Nat) (llv1 : Nat) : Nat :=\n  Nat.add llv0 llv1"
            );
            let checked = support::checked_project(support::shared_corpus_project());
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
                lean.contains(
                    "@[expose] public def good : Prop :=\n  Exists (fun (llv0 : Nat) => Eq llv0 llv0)\n"
                ),
                "a predicate def returns Prop: {lean}"
            );
            if let Some(fixture) = support::corpus_backed("DF-03") {
                assert_eq!(fixture.attestation["status"], "verified");
            }
            assert_eq!(
                support::corpus_declaration_lean("even"),
                "@[expose] public def even (llv0 : Nat) : Prop :=\n  Exists (fun (llv1 : Nat) => Eq llv0 (Nat.add llv1 llv1))"
            );
            assert_eq!(
                support::corpus_declaration_lean("double_even"),
                "public theorem double_even (llv0 : Nat) : LexLeanExample.Main.even (LexLeanExample.Main.double llv0) := by\n  refine ⟨llv0, ?_⟩\n  rfl"
            );
            let checked = support::checked_project(support::shared_corpus_project());
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
                .linked_json()
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
        // §17.11: generic semantic declarations are checked before either
        // fixed backend and generate source that the kernel verifies.
        "DF-11" => {
            let project = support::semantic_project();
            project.check_ok();
            let checked = support::checked_project(&project);
            let semantic = checked.modules["Main"]
                .document
                .semantic
                .as_ref()
                .expect("semantic module");
            support::assert_schema(
                "semantic-module",
                "language-1.1 semantic fixture",
                &serde_json::to_value(semantic).expect("semantic JSON"),
            );
            let rendered = support::rendered(&project);
            let lean = support::lean_text(&rendered, "Main");
            for expected in [
                "public inductive ComponentKind",
                "public structure Box (A : Type)",
                "public structure Component",
                "public class Validatable",
                "public instance (priority := 1000) defaultValidatable",
                "public def allConsecutive",
                "| expected, List.cons value rest =>",
                "public theorem allConsecutive_sound_complete",
                "cases value with",
                "induction values with",
                "simp only [allConsecutive]",
            ] {
                assert!(
                    lean.contains(expected),
                    "generated Lean contains `{expected}`:\n{lean}"
                );
            }
            assert!(!lean.contains("sorry") && !lean.contains("axiom"));
            let tex_path = rendered
                .files
                .iter()
                .find(|(path, _)| path.ends_with(".tex"))
                .map(|(_, bytes)| String::from_utf8(bytes.clone()).expect("utf8"))
                .expect("LaTeX");
            for expected in ["ComponentKind", "Validatable", "allConsecutive"] {
                assert!(tex_path.contains(expected), "LaTeX contains {expected}");
            }
            let verified = support::verify_ok_backed("DF-11", &project);
            if let Some(attestation) = verified {
                assert!(attestation.root.as_std_path().is_dir());
                assert_ne!(attestation.attestation_id, lexlean::Sha256Digest([0; 32]));
            }

            let mutations = [
                ("\"priority\":1000", "\"priority\":999"),
                ("\"name\":\"sampleComponent\"", "\"name\":\"ComponentKind\""),
                (
                    "\"member\":{\"name\":\"Component\"}",
                    "\"member\":{\"name\":\"MissingType\"}",
                ),
                (
                    "{\"kind\":\"var\",\"name\":\"rest\"}]",
                    "{\"kind\":\"var\",\"name\":\"values\"}]",
                ),
                (
                    "\"spec\":\"lexlean/semantic-module/1\"",
                    "\"lean\":\"def escaped := true\",\"spec\":\"lexlean/semantic-module/1\"",
                ),
                (
                    "\"recursive_argument\":\"values\",\"result\":{\"kind\":\"bool\"}",
                    "\"recursive_argument\":\"values\",\"result\":{\"kind\":\"nat\"}",
                ),
                (
                    "\"field\":\"index\",\"value\":{\"kind\":\"nat\",\"value\":\"0\"}",
                    "\"field\":\"index\",\"value\":{\"kind\":\"bool\",\"value\":true}",
                ),
                (
                    "\"binders\":[],\"body\":{\"kind\":\"bool\",\"value\":true},\"constructor\":{\"name\":\"List.nil\"}",
                    "\"binders\":[],\"body\":{\"kind\":\"nat\",\"value\":\"0\"},\"constructor\":{\"name\":\"List.nil\"}",
                ),
            ];
            for (from, to) in mutations {
                let invalid = support::semantic_project();
                invalid.edit("src/Main.lex.tex", from, to);
                let error = invalid.check_err();
                support::expect_code(&error, "LLT4001");
                assert!(
                    !invalid.root.join(".lexlean/build").as_std_path().exists(),
                    "semantic rejection occurs before a backend"
                );
            }

            let nonexhaustive = support::semantic_project();
            let source = nonexhaustive.read("src/Main.lex.tex");
            let start = source.find("{\"binders\":[],\"body\":{\"kind\":\"bool\",\"value\":true},\"constructor\":{\"name\":\"List.nil\"}},")
                .expect("nil branch");
            let needle = "{\"binders\":[],\"body\":{\"kind\":\"bool\",\"value\":true},\"constructor\":{\"name\":\"List.nil\"}},";
            let mut changed = source;
            changed.replace_range(start..start + needle.len(), "");
            nonexhaustive.write("src/Main.lex.tex", &changed);
            nonexhaustive.check_fails_with("LLT4001");

            // Imported semantic declarations participate in the same typed
            // environment. A remote call cannot bypass arity or result-type
            // checking merely because its declaration is in another module.
            let remote_arity = support::P::semantic_example();
            remote_arity.edit(
                "src/Main.lex.tex",
                r#""arguments":[],"function":{"module":"Support","name":"remoteEnabled"}"#,
                r#""arguments":[{"kind":"nat","value":"0"}],"function":{"module":"Support","name":"remoteEnabled"}"#,
            );
            remote_arity.check_fails_with("LLT4001");

            let remote_result = support::P::semantic_example();
            remote_result.edit(
                "src/Support.lex.tex",
                r#""body":{"kind":"bool","value":true},"kind":"definition","name":"remoteEnabled","parameters":[],"result":{"kind":"bool"}"#,
                r#""body":{"kind":"nat","value":"0"},"kind":"definition","name":"remoteEnabled","parameters":[],"result":{"kind":"nat"}"#,
            );
            remote_result.check_fails_with("LLT4001");

            for (from, to) in [
                (
                    r#""value":{"arguments":[{"kind":"nat"}],"class":{"module":"VariantTypes","name":"DefaultValue"},"kind":"instance_value""#,
                    r#""value":{"arguments":[{"kind":"unit"}],"class":{"module":"VariantTypes","name":"DefaultValue"},"kind":"instance_value""#,
                ),
                (
                    r#""resolved":{"module":"VariantTypes","name":"natDefault"}"#,
                    r#""resolved":{"name":"natUsesDefault"}"#,
                ),
                (
                    r#""class":{"name":"UsesDefault"},"fields""#,
                    r#""class":{"module":"VariantTypes","name":"DefaultValue"},"fields""#,
                ),
            ] {
                let invalid = support::semantic_project();
                invalid.edit("src/VariantInstances.lex.tex", from, to);
                invalid.check_fails_with("LLT4001");
            }

            // Every conservative rejection promised by §17.11 occurs while
            // linking semantic data, before either fixed backend is entered.
            for (path, from, to) in [
                (
                    "src/VariantTypes.lex.tex",
                    r#""name":"MaybeNat","parameters":[]"#,
                    r#""name":"MaybeNat","parameters":[{"name":"index","type":{"kind":"nat"}}]"#,
                ),
                (
                    "src/VariantTypes.lex.tex",
                    r#"{"fields":[{"kind":"nat"}],"name":"some"}"#,
                    r#"{"fields":[{"arguments":[],"kind":"named","member":{"name":"MaybeNat"}}],"name":"some"}"#,
                ),
                (
                    "src/VariantTypes.lex.tex",
                    r#"{"fields":[],"name":"none"},{"fields""#,
                    r#"{"fields":[],"name":"some"},{"fields""#,
                ),
                (
                    "src/VariantTerms.lex.tex",
                    r#""kind":"definition","name":"chooseNat""#,
                    r#""kind":"definition","name":"chooseNat","recursive_argument":"flag""#,
                ),
                (
                    "src/VariantTerms.lex.tex",
                    r#""binders":["prior"],"body""#,
                    r#""binders":[],"body""#,
                ),
                (
                    "src/Main.lex.tex",
                    r#",{"binders":[],"constructor":"database","proof":{"kind":"reflexivity"}}"#,
                    "",
                ),
                (
                    "src/Main.lex.tex",
                    r#""binders":["head","tail","ih"],"constructor":"cons""#,
                    r#""binders":["head","tail"],"constructor":"cons""#,
                ),
                (
                    "src/Main.lex.tex",
                    r#""definitions":[{"name":"allConsecutive"}]"#,
                    r#""definitions":[{"name":"missingDefinition"}]"#,
                ),
                (
                    "src/Main.lex.tex",
                    r#""kind":"induction","scrutinee":"values""#,
                    r#""generalizing":["missing"],"kind":"induction","scrutinee":"values""#,
                ),
                (
                    "src/VariantProofs.lex.tex",
                    r#""kind":"apply","theorem":{"name":"conjunction_refl"}"#,
                    r#""kind":"apply","theorem":{"name":"missingTheorem"}"#,
                ),
                (
                    "src/VariantProofs.lex.tex",
                    r#"{"expected":"0","field":"left"},{"expected":"1","field":"right"}"#,
                    r#"{"expected":"0","field":"left"}"#,
                ),
            ] {
                let invalid = support::semantic_project();
                invalid.edit(path, from, to);
                invalid.check_fails_with("LLT4001");
                assert!(
                    !invalid.root.join(".lexlean/build").as_std_path().exists(),
                    "semantic rejection occurs before a backend"
                );
            }
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
