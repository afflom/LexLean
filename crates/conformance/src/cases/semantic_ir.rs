//! The `semantic-ir` suite: SM-01..SM-14.

use std::collections::BTreeSet;

use sha2::Digest;

use crate::support::{self, P};

/// Every `"k"` and `"kind"` tag value in a canonical JSON document.
fn collect_tags(value: &serde_json::Value, key: &str, out: &mut BTreeSet<String>) {
    match value {
        serde_json::Value::Object(map) => {
            if let Some(serde_json::Value::String(tag)) = map.get(key) {
                out.insert(tag.clone());
            }
            for child in map.values() {
                collect_tags(child, key, out);
            }
        }
        serde_json::Value::Array(items) => {
            for child in items {
                collect_tags(child, key, out);
            }
        }
        _ => {}
    }
}

fn linked_json(project: &P) -> serde_json::Value {
    let checked = support::checked_project(project);
    serde_json::from_str(&checked.linked.to_json().to_canonical_string())
        .expect("linked IR is canonical JSON")
}

pub(crate) fn run(id: &str) {
    match id {
        // §17.1: phases run in order; nothing reaches a backend unlinked.
        "SM-01" => {
            // A normalization error and an unknown word in one file: the
            // earlier phase reports.
            let project = P::example();
            project.edit(
                "src/Main.lex.tex",
                "For every natural",
                "\tFor every banana natural",
            );
            let error = project.check_err();
            assert_eq!(
                error.diagnostics.first().map(|d| d.code.as_str()),
                Some("LLL1002"),
                "normalization precedes lexical resolution"
            );

            // A failed check emits no build artifacts.
            let failing = P::example();
            failing.edit(
                "src/Main.lex.tex",
                "For every natural",
                "For every banana natural",
            );
            let _ = failing
                .engine()
                .build(lexlean::BuildRequest {
                    selection: lexlean::Selection::Entrypoints,
                })
                .err()
                .expect("a build on a failing project fails");
            assert!(
                !failing.root.join(".lexlean/build").as_std_path().exists(),
                "no backend output exists for an unlinked program"
            );
        }
        // §17.2: closed reference kinds with stable identity.
        "SM-02" => {
            let project = support::defs_project();
            let mut kinds = BTreeSet::new();
            collect_tags(&linked_json(&project), "kind", &mut kinds);
            // The `kind` key also tags declaration kinds and policy kinds;
            // all three vocabularies are closed.
            let allowed: BTreeSet<String> = [
                "core",
                "external",
                "document",
                "defined",
                "typedefinition",
                "termdefinition",
                "predicatedefinition",
                "theorem",
                "lemma",
                "corollary",
                "none",
                "allow",
                "exact",
            ]
            .into_iter()
            .map(str::to_owned)
            .collect();
            assert!(!kinds.is_empty(), "the fixture exercises reference kinds");
            assert!(
                kinds.is_subset(&allowed),
                "closed reference kinds only, found {kinds:?}"
            );
            // Stable identity: a second run reproduces the bytes and IDs.
            let first = support::checked_project(&project);
            let second = support::checked_project(&project);
            assert_eq!(first.semantic_id, second.semantic_id);
            assert_eq!(
                first.linked.to_json().to_canonical_string(),
                second.linked.to_json().to_canonical_string()
            );
        }
        // §17.3: term IR is exactly the closed variant set.
        "SM-03" | "SM-04" => {
            let mut tags = BTreeSet::new();
            for project in [P::example(), support::defs_project()] {
                collect_tags(&linked_json(&project), "k", &mut tags);
            }
            let allowed: BTreeSet<String> = [
                // §17.3 terms.
                "sort",
                "local",
                "global",
                "app",
                "pi",
                "lam",
                "let",
                "nat",
                // §17.4 proofs.
                "seq",
                "intro",
                "exact",
                "apply-one",
                "apply",
                "rfl",
                "witness",
                "left",
                "right",
                "have",
                "rw",
                "simp-only",
                "constructor",
                "cases",
                "induction",
                "calc",
                // §17.5 document phrase items and blocks.
                "word",
                "math",
                "punct",
                "declaration",
                "section",
                "definition",
                "theorem",
            ]
            .into_iter()
            .map(str::to_owned)
            .collect();
            assert!(
                tags.is_subset(&allowed),
                "closed IR variant tags only, found extras: {:?}",
                tags.difference(&allowed).collect::<Vec<_>>()
            );
            for expected in ["app", "pi", "global", "rfl"] {
                assert!(tags.contains(expected), "the corpus exercises `{expected}`");
            }
        }
        // §17.6: conservative checks without kernel claims; an ill-typed
        // glossary application (too many explicit arguments) is rejected at
        // conversion with the entry named (S5).
        "SM-05" => {
            let overapplied = P::example();
            overapplied.add_package(
                "lexicons/test-arity",
                "test.arity",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[
                    (
                        "nzz.toml",
                        &support::nzz_entry("Nat.le_refl").replace(
                            "(app (const lexlean.core::lnot) (app (const lexlean.std.nat::ne) (local n) (local n)))",
                            "(app (const lexlean.core::lnot) (app (const lexlean.std.nat::ne) (local n) (local n) (local n)))",
                        ),
                    ),
                    ("z.toml", Z_MATH),
                ],
            );
            overapplied.write(
                "src/Main.lex.tex",
                &support::nzz_module(&["test.arity@1.0.0"]),
            );
            overapplied.relock();
            let error = overapplied.check_err();
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLT4001")
                .unwrap_or_else(|| panic!("LLT4001 for an over-applied signature: {error}"));
            assert!(
                diagnostic.message.contains("lexlean.std.nat::ne")
                    && diagnostic.message.contains("3 explicit arguments"),
                "the diagnostic names the entry and the arity: {}",
                diagnostic.message
            );

            let ill_typed = P::example();
            ill_typed.edit(
                "src/Main.lex.tex",
                "\\(n + 0 = n\\)",
                "\\(n + 0 = n\\) and \\(n + 0\\)",
            );
            let error = ill_typed.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLT4001" | "LLP2001")),
                "a non-proposition conjunct fails conservative elaboration: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §17.3: omitted implicits recorded; user holes rejected.
        "SM-06" => {
            let project = P::example();
            let json = support::checked_project(&project)
                .linked
                .to_json()
                .to_canonical_string();
            assert!(
                json.contains("\"i\":["),
                "the Eq application records its omitted implicit binder: {json}"
            );
            let hole = P::example();
            hole.edit("src/Main.lex.tex", "\\(n + 0 = n\\)", "\\(n + _ = n\\)");
            hole.check_fails_with("LLL1004");
        }
        // §17.7: canonical signature comparison is alpha-safe.
        "SM-07" => {
            let project = support::defs_project();
            project.edit(
                "lexicons/test-defs/entries/double.toml",
                "(pi ((explicit n (const lexlean.std.nat::nat)))",
                "(pi ((explicit renamed (const lexlean.std.nat::nat)))",
            );
            project.relock();
            project.check_ok();
        }
        // §17.8: deterministic, collision-checked name generation.
        "SM-08" => {
            let project = P::example();
            let first = support::rendered(&project);
            let second = support::rendered(&project);
            assert_eq!(
                support::lean_text(&first, "Main"),
                support::lean_text(&second, "Main"),
                "generated names are deterministic"
            );

            let clash = P::example();
            let body = clash.read("src/Main.lex.tex");
            let second_theorem = "\n\\begin{theorem}{add-zero}\n\\noaxioms\nFor every natural number \\(m\\), \\(m + 0 = m\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}";
            clash.write(
                "src/Main.lex.tex",
                &body.replace("\n\\end{lexlean}", second_theorem),
            );
            let error = clash.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2003" | "LLR3002")),
                "a duplicate component ID is a collision: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
            // A component converting to a pinned-Lean keyword is rejected
            // by name (C9); tactic names are not keywords.
            for keyword in [
                "def", "theorem", "at", "where", "instance", "with", "then", "let",
            ] {
                let project = P::example();
                project.edit(
                    "src/Main.lex.tex",
                    "\\begin{theorem}{add-zero}",
                    &format!("\\begin{{theorem}}{{{keyword}}}"),
                );
                let error = project.check_fails_with("LLP2003");
                let diagnostic = error
                    .diagnostics
                    .iter()
                    .find(|d| d.code.as_str() == "LLP2003")
                    .expect("matched");
                assert!(
                    diagnostic.message.contains("Lean keyword") && diagnostic.primary.is_some(),
                    "`{keyword}`: {}",
                    diagnostic.message
                );
            }
            for name in ["first", "left", "apply", "cases"] {
                let project = P::example();
                project.edit(
                    "src/Main.lex.tex",
                    "\\begin{theorem}{add-zero}",
                    &format!("\\begin{{theorem}}{{{name}}}"),
                );
                project.check_ok();
            }
        }
        // §17.9: alpha-safe serialization with dense binder indices.
        "SM-09" => {
            let with_n = P::example();
            let with_m = P::example();
            with_m.write(
                "src/Main.lex.tex",
                &with_n
                    .read("src/Main.lex.tex")
                    .replace("(n", "(m")
                    .replace("= n", "= m"),
            );
            let key = |project: &P| {
                let checked = support::checked_project(project);
                let module = &checked.modules["Main"];
                let declaration = module
                    .document
                    .declarations()
                    .into_iter()
                    .find(|d| d.component == "add-zero")
                    .expect("the theorem");
                match &declaration.body {
                    lexlean::ir::declaration::DeclBody::TheoremLike { statement, .. } => {
                        statement.canonical_key()
                    }
                    lexlean::ir::declaration::DeclBody::Definition { .. } => {
                        panic!("the fixture is a theorem")
                    }
                }
            };
            assert_eq!(
                key(&with_n),
                key(&with_m),
                "alpha-renamed statements share one canonical key"
            );
        }
        // §21.3: the source ID is exactly the specified framed hash.
        "SM-10" => {
            let project = P::example();
            let inner =
                lexlean::project::Project::load(&project.root.join("lexlean.toml")).expect("load");
            let checked = support::checked_project(&project);
            let mut hasher = sha2::Sha256::new();
            hasher.update(b"lexlean-source-v1\0");
            let frame = |hasher: &mut sha2::Sha256, label: &str, bytes: &[u8]| {
                hasher.update(u32::try_from(label.len()).expect("short").to_be_bytes());
                hasher.update(label.as_bytes());
                hasher.update((bytes.len() as u64).to_be_bytes());
                hasher.update(bytes);
            };
            frame(
                &mut hasher,
                "project",
                inner.config.canonical_toml().as_bytes(),
            );
            frame(&mut hasher, "lock", &checked.canonical_lock);
            frame(&mut hasher, "path", b"src/Main.lex.tex");
            frame(
                &mut hasher,
                "source",
                checked.modules["Main"].normalized.as_bytes(),
            );
            let manual: [u8; 32] = hasher.finalize().into();
            assert_eq!(
                lexlean::artifact::content_id::Sha256Digest(manual),
                checked.source_id,
                "§21.3: the source ID equals its manual recomputation"
            );

            // §21.4: the semantic ID is the specified function of the
            // linked IR and closure serializations.
            let module_closure = checked
                .closure
                .closure_json("", &checked.visible_union)
                .to_canonical_string();
            let recomputed = lexlean::artifact::content_id::semantic_id(
                lexlean::compiler_semantics_id(),
                &checked.linked.to_json().to_canonical_string(),
                &module_closure,
            );
            assert_eq!(
                recomputed, checked.semantic_id,
                "§21.4: the semantic ID equals the specified framed inputs"
            );
        }
        // §24.4: complete result sets in stable order.
        "SM-11" => {
            let project = P::example();
            project.write(
                "src/Helper.lex.tex",
                &project
                    .read("src/Main.lex.tex")
                    .replace("{Main}", "{Helper}"),
            );
            project.edit(
                "src/Main.lex.tex",
                "\\useglossary{lexlean.std.nat@1.0.0}",
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\importmodule{Helper}",
            );
            let checked = project.check_ok();
            let names: Vec<&String> = checked.units.keys().collect();
            assert_eq!(
                names,
                ["Helper", "Main"],
                "sorted, each module exactly once"
            );
            let all = project
                .engine()
                .check(lexlean::CheckRequest {
                    selection: lexlean::Selection::All,
                })
                .expect("--all checks");
            assert_eq!(
                all.units.keys().collect::<Vec<_>>(),
                names,
                "every selection returns the same complete sorted set"
            );
        }
        // §17.5, I7: no opaque prose inside semantic IR.
        "SM-12" => {
            let project = P::example();
            let json = support::checked_project(&project)
                .linked
                .to_json()
                .to_canonical_string();
            for prose in [
                "natural number",
                "For every",
                "reflexivity",
                "Close the goal",
            ] {
                assert!(
                    !json.contains(prose),
                    "linked IR must not embed source prose ({prose:?})"
                );
            }
        }
        // §15.4: inherited parameters are explicit, and emitted only where
        // used.
        "SM-13" => {
            let project = P::example();
            project.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{section}{basics}\n\\heading{Natural number addition}\n\\parameters{natural number \\(p\\)}\n\\begin{theorem}{uses-param}\n\\noaxioms\n\\(p + 0 = p\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\begin{theorem}{ignores-param}\n\\noaxioms\nFor every natural number \\(m\\), \\(m + 0 = m\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{section}\n\\end{lexlean}\n",
            );
            let checked = support::checked_project(&project);
            let module = &checked.modules["Main"];
            let params_of = |component: &str| {
                module
                    .document
                    .declarations()
                    .into_iter()
                    .find(|d| d.component == component)
                    .unwrap_or_else(|| panic!("{component} exists"))
                    .params
                    .len()
            };
            assert_eq!(
                params_of("uses-param"),
                1,
                "the using theorem inherits the binder"
            );
            assert_eq!(params_of("ignores-param"), 0, "the non-user emits none");
            // A reference to a parameterized declaration applies the
            // parameters explicitly, inside and outside its section, and
            // Lean-verifies (C2, S4).
            let fixture = support::verified_corpus();
            assert_eq!(fixture.attestation["status"], "verified");
            assert_eq!(
                support::corpus_declaration_lean("use_inside"),
                "public theorem use_inside (llv0 : Nat) : Eq (Nat.succ (Nat.add llv0 0)) (Nat.succ llv0) := by\n  apply LexLeanExample.Main.succ_congr\n  exact LexLeanExample.Main.param_add_zero llv0"
            );
            assert_eq!(
                support::corpus_declaration_lean("use_outside"),
                "public theorem use_outside (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  exact LexLeanExample.Main.param_add_zero llv0"
            );
            // The bare reference has the parameter-abstracted type: it does
            // not close a goal that expects the instantiated statement.
            let bare = support::corpus_project();
            bare.edit(
                "src/Main.lex.tex",
                "Close the goal with \\(\\reference{Main::param-add-zero}(q)\\).",
                "Close the goal with \\(\\reference{Main::param-add-zero}\\).",
            );
            bare.check_fails_with("LLT4001");
        }
        // §15.5: numerals require a unique expected type.
        "SM-14" => {
            let project = P::example();
            project.edit("src/Main.lex.tex", "\\(n + 0 = n\\)", "\\(1 = 1\\)");
            let error = project.check_err();
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLT4001")
                .unwrap_or_else(|| {
                    panic!("a numeral without a unique expected type is LLT4001: {error}")
                });
            assert!(
                diagnostic.message.contains("numeral `1`") && diagnostic.primary.is_some(),
                "the numeral is named: {}",
                diagnostic.message
            );
            // A numeral typed by a binder, an operator, or a witness slot is
            // accepted (corpus: `Use \\(0\\) as the witness`, `\\(0\\) is even`).
            let fixture = support::verified_corpus();
            assert_eq!(fixture.attestation["status"], "verified");
            assert_eq!(
                support::corpus_declaration_lean("zero_even"),
                "public theorem zero_even : LexLeanExample.Main.even 0 := by\n  refine ⟨0, ?_⟩\n  rfl"
            );
        }
        other => panic!("no semantic-ir case is wired for {other}"),
    }
}

/// The math-channel zero used by the arity fixture.
const Z_MATH: &str = r#"spec = "lexlean/entry/1"
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
