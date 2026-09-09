//! The `semantic-ir` suite: SM-01..SM-22.

use std::collections::BTreeSet;
use std::process::Command;

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
    serde_json::from_str(&checked.linked_json().to_canonical_string())
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
                first.linked_json().to_canonical_string(),
                second.linked_json().to_canonical_string()
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
            // An over-applied signature is rejected when the lexicon closure
            // is built (§13.7: the signature is checked as an interface), so
            // it never reaches source elaboration.
            overapplied.relock();
            let error = overapplied.check_err();
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLR3004")
                .unwrap_or_else(|| panic!("LLR3004 for an over-applied signature: {error}"));
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

            // Expected types are read through definitions (§17.6, §17.7):
            // a binder typed by a document type definition satisfies `+`,
            // and a defined type noun (`natural number list`) meets a
            // polymorphic constant in either argument order — the solved
            // metavariable's solution unfolds too.
            support::f1_exact("SM-05", 
                "count_add_zero",
                "public theorem count_add_zero (llv0 : LexLeanExample.Main.count) : Eq (Nat.add llv0 0) llv0 := by\n  rfl",
            );
            support::f1_exact("SM-05", 
                "list_nil",
                "public theorem list_nil (llv0 : (List Nat)) : (Eq llv0 List.nil) → Eq List.nil llv0 := by\n  intro llh0\n  rw [llh0]",
            );
            // The core arrow elaborates in math to a non-dependent `Pi`
            // (§15.6), and the canonical formatter spells it back as `→`
            // inside an island where prose cannot hold it.
            support::f1_exact("SM-05", 
                "arrow_or",
                "public theorem arrow_or (llv0 : Prop) : Or (llv0 → llv0) llv0 := by\n  left\n  intro llh0\n  exact llh0",
            );
            let formatted = support::f1_project();
            formatted
                .engine()
                .format(lexlean::FormatRequest {
                    selection: lexlean::Selection::Entrypoints,
                    check_only: false,
                })
                .expect("the WS-F1 module formats");
            let source = formatted.read("src/Main.lex.tex");
            assert!(
                source.contains("\\(p → p\\) or \\(p\\)"),
                "the arrow inside an island keeps its math form: {source}"
            );
            formatted.fmt_check_ok();
            formatted.check_ok();
            // A rejection names why its candidates died (§20.1): an infix
            // entry whose document declaration is not yet available leaves
            // no candidate, and the `LLT4001` carries the reason as a note.
            let unavailable = support::f1_project();
            unavailable.edit(
                "src/Main.lex.tex",
                "For every count \\(c\\), \\(c + 0 = c\\).",
                "For every natural number \\(c\\), \\(c ⊕ 0 = c\\).",
            );
            let error = unavailable.check_err();
            let rejected = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLT4001")
                .unwrap_or_else(|| panic!("an uninstantiable operator is LLT4001: {error}"));
            assert!(
                rejected.notes.iter().any(|note| {
                    note.message.contains("test.f1::oplus")
                        && note.message.contains("Main::oplus")
                        && note.message.contains("not available")
                }),
                "the note names the entry and why it cannot be instantiated: {rejected:#?}"
            );
        }
        // §17.3: omitted implicits recorded; user holes rejected.
        "SM-06" => {
            let project = P::example();
            let json = support::checked_project(&project)
                .linked_json()
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

            // A binder nothing references keeps its §17.8 index and carries
            // the `_` prefix that marks a deliberate binding: pinned Lean's
            // unused-variable linter warns otherwise, and a warning fails
            // verification (§20.2). The theorem still states, and proves,
            // the quantified proposition the source wrote.
            let unused = P::example();
            unused.edit(
                "src/Main.lex.tex",
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "For every natural number \\(n\\) and natural number \\(m\\), \\(n + 0 = n\\).",
            );
            let lean = support::lean_text(&support::rendered(&unused), "Main");
            assert!(
                lean.contains(
                    "public theorem add_zero (llv0 : Nat) (_llv1 : Nat) : Eq (Nat.add llv0 0) llv0 := by"
                ),
                "an unreferenced lifted binder is `_llv1`: {lean}"
            );
            support::verify_ok_backed("SM-08", &unused);

            let unused_hypothesis = P::example();
            unused_hypothesis.edit(
                "src/Main.lex.tex",
                "For every natural number \\(n\\), \\(n + 0 = n\\).\n\\begin{proof}\nClose the goal by reflexivity.",
                "For every natural number \\(n\\), if \\(n = n\\), then \\(n + 0 = n\\).\n\\begin{proof}\nAssume \\(h\\).\nClose the goal by reflexivity.",
            );
            let lean = support::lean_text(&support::rendered(&unused_hypothesis), "Main");
            assert!(
                lean.contains("  intro _llh0\n"),
                "an unreferenced introduced hypothesis is `_llh0`: {lean}"
            );
            support::verify_ok_backed("SM-08", &unused_hypothesis);
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
                &checked.linked_json().to_canonical_string(),
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
                .linked_json()
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
            if let Some(fixture) = support::corpus_backed("SM-13") {
                assert_eq!(fixture.attestation["status"], "verified");
            }
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
            if let Some(fixture) = support::corpus_backed("SM-14") {
                assert_eq!(fixture.attestation["status"], "verified");
            }
            assert_eq!(
                support::corpus_declaration_lean("zero_even"),
                "public theorem zero_even : LexLeanExample.Main.even 0 := by\n  refine ⟨(0 : Nat), ?_⟩\n  rfl"
            );
        }
        // §17.10: a native core module is semantic data, not backend text.
        "SM-15" => {
            const CORE_SOURCE: &str = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\\begin{coremodule}\n\\coredata{{\"declarations\":[{\"class\":false,\"generated\":false,\"kind\":\"theorem\",\"levels\":[],\"name\":\"CoreFixture.truth\",\"policy\":{\"kind\":\"none\"},\"transparency\":\"semireducible\",\"type\":0,\"value\":1}],\"imports\":[\"Init\"],\"nodes\":[{\"k\":\"c\",\"n\":\"True\",\"u\":[]},{\"k\":\"c\",\"n\":\"True.intro\",\"u\":[]}],\"proof_nodes\":[1],\"spec\":\"lexlean/core-module/1\"}}\n\\end{coremodule}\n\\end{lexlean}\n";
            let project = P::example();
            project.write("src/Main.lex.tex", CORE_SOURCE);
            let checked = support::checked_project(&project);
            let document = &checked.modules["Main"].document;
            let core = document.core.as_ref().expect("native core module");
            assert!(
                document.blocks.is_empty(),
                "native and prose forms are exclusive"
            );
            assert_eq!(core.nodes.len(), 2);
            assert_eq!(core.declarations.len(), 1);
            assert_eq!(core.declarations[0].policy.kind(), "none");
            support::assert_schema(
                "core-module",
                "native core fixture",
                &serde_json::to_value(core).expect("core JSON"),
            );

            let built = project.build_ok();
            let build_root = project.build_dir(&built.build_id.expect("build id"));
            let unit = &built.units["Main"];
            let mut lean = None;
            let mut tex = None;
            for relative in &unit.artifacts.paths {
                let text = std::fs::read_to_string(build_root.join(relative).as_std_path())
                    .expect("generated artifact");
                if relative.ends_with(".lean") {
                    lean = Some(text);
                } else if relative.ends_with(".tex") {
                    tex = Some(text);
                }
            }
            let lean = lean.expect("generated Lean");
            let tex = tex.expect("generated LaTeX");
            assert!(
                lean.contains("LexLeanCore.Runtime.decodeAndAdd")
                    && lean.contains("CoreFixture.truth"),
                "Lean reconstructs the same native declaration"
            );
            assert!(
                tex.contains("CoreFixture.truth") && tex.contains("True.intro"),
                "LaTeX traverses the same type and proof DAG"
            );
            let _ = support::verify_ok_backed("SM-15", &project);

            let invalid = P::example();
            invalid.write(
                "src/Main.lex.tex",
                &CORE_SOURCE.replace(
                    "\"imports\":[\"Init\"]",
                    "\"imports\":[\"Init\"],\"lean\":\"theorem truth := True.intro\"",
                ),
            );
            invalid.check_fails_with("LLI9001");
        }
        // §17.11, §24.1: the public snapshot carries every high-level
        // semantic variant as owned nested data and remains backend-free.
        "SM-16" => {
            let project = support::semantic_project();
            let engine = project.engine();
            let request = || lexlean::CheckRequest {
                selection: lexlean::Selection::Entrypoints,
            };
            let first = engine.snapshot(request()).expect("snapshot");
            let second = engine.snapshot(request()).expect("repeat snapshot");
            let _built = project.build_ok();
            let third = engine.snapshot(request()).expect("post-build snapshot");
            assert_eq!(first.canonical_bytes(), second.canonical_bytes());
            assert_eq!(first.canonical_bytes(), third.canonical_bytes());
            assert_eq!(first.snapshot_id(), second.snapshot_id());
            assert_eq!(first.snapshot_id(), third.snapshot_id());
            assert_eq!(first.language(), "1.1");
            let module = first
                .modules()
                .iter()
                .find(|module| module.name() == "Main")
                .expect("the all-declaration-variant Main module");
            assert!(module.core().is_none());
            let semantic = module.semantic().expect("typed semantic module");
            let typed_kinds = semantic
                .declarations
                .iter()
                .map(lexlean::SnapshotSemanticDeclaration::kind)
                .collect::<BTreeSet<_>>();
            assert_eq!(
                typed_kinds,
                BTreeSet::from([
                    "class",
                    "definition",
                    "inductive",
                    "instance",
                    "structure",
                    "theorem",
                ]),
                "every declaration variant is readable through stable public snapshot types"
            );
            support::check_downstream_snapshot_api();
            let value: serde_json::Value =
                serde_json::from_slice(&first.canonical_bytes()).expect("JSON");
            support::assert_schema("semantic-snapshot", "1.1 all-variant snapshot", &value);
            let mut kinds = BTreeSet::new();
            collect_tags(&value, "kind", &mut kinds);
            for expected in [
                "structure",
                "class",
                "instance",
                "inductive",
                "definition",
                "theorem",
                "var",
                "nat",
                "bool",
                "unit",
                "nil",
                "cons",
                "record",
                "constructor",
                "instance_value",
                "project",
                "call",
                "if",
                "match",
                "eq",
                "le",
                "lt",
                "add",
                "beq",
                "ble",
                "blt",
                "and",
                "prop_and",
                "or",
                "not",
                "implies",
                "iff",
                "forall",
                "cases",
                "induction",
                "simplify",
                "reflexivity",
                "decide",
                "congruence",
                "boolean_reflection",
                "apply",
            ] {
                assert!(
                    kinds.contains(expected),
                    "snapshot exercises `{expected}`: {kinds:?}"
                );
            }
            let bytes = String::from_utf8(first.canonical_bytes()).expect("utf8");
            assert!(
                bytes.contains("\"axiom_policy\":{\"axioms\":[\"propext\"],\"kind\":\"exact\"}"),
                "snapshot retains a nonempty exact semantic theorem policy"
            );
            if let Some(verified) = support::verify_ok_backed("SM-16", &project) {
                let attestation: serde_json::Value = serde_json::from_slice(
                    &std::fs::read(verified.root.join("attestation.json").as_std_path())
                        .expect("language-1.1 attestation"),
                )
                .expect("attestation JSON");
                let expected =
                    lexlean::compiler_semantics_id_for(lexlean::LATEST_LANGUAGE_VERSION).to_hex();
                assert_eq!(
                    attestation["lexlean"]["compiler_semantics"].as_str(),
                    Some(expected.as_str()),
                    "language-1.1 attestation binds the selected compiler semantics"
                );
            }
            assert!(!bytes.contains(project.root.as_str()));
            assert!(!bytes.contains("public structure"));
            assert!(!bytes.contains("namespace SemanticFixture"));
        }
        "SM-17" => {
            let project = support::semantic_project();
            let snapshot = project
                .engine()
                .snapshot(lexlean::CheckRequest {
                    selection: lexlean::Selection::Entrypoints,
                })
                .expect("portable snapshot");
            let value: serde_json::Value =
                serde_json::from_slice(&snapshot.canonical_bytes()).expect("snapshot JSON");
            let mut kinds = BTreeSet::new();
            collect_tags(&value, "kind", &mut kinds);
            for expected in [
                "int", "int8", "int16", "int32", "int64", "uint8", "uint16", "uint32", "uint64",
                "string", "bytes", "option", "result",
            ] {
                assert!(kinds.contains(expected), "missing portable type {expected}");
            }
            let text = String::from_utf8(snapshot.canonical_bytes()).expect("utf8 snapshot");
            for representation in [
                "int", "int8", "int16", "int32", "int64", "uint8", "uint16", "uint32", "uint64",
            ] {
                assert!(
                    text.contains(&format!("\"representation\":\"{representation}\"")),
                    "missing literal representation {representation}"
                );
            }
            assert!(text.contains("\"hex\":\"aabb7fff\""));
        }
        "SM-18" => {
            let project = support::semantic_project();
            let snapshot = project
                .engine()
                .snapshot(lexlean::CheckRequest {
                    selection: lexlean::Selection::Entrypoints,
                })
                .expect("portable snapshot");
            let value: serde_json::Value =
                serde_json::from_slice(&snapshot.canonical_bytes()).expect("snapshot JSON");
            fn operations(value: &serde_json::Value, out: &mut BTreeSet<String>) {
                match value {
                    serde_json::Value::Object(map) => {
                        if let Some(serde_json::Value::String(operation)) = map.get("operation") {
                            out.insert(operation.clone());
                        }
                        for child in map.values() {
                            operations(child, out);
                        }
                    }
                    serde_json::Value::Array(items) => {
                        for child in items {
                            operations(child, out);
                        }
                    }
                    _ => {}
                }
            }
            let mut found = BTreeSet::new();
            operations(&value, &mut found);
            let expected = BTreeSet::from([
                "append",
                "bit_and",
                "bit_not",
                "bit_or",
                "bit_xor",
                "checked_add",
                "checked_convert",
                "checked_multiply",
                "checked_negate",
                "checked_quotient",
                "checked_subtract",
                "compare_bytes",
                "equal",
                "format_decimal",
                "index",
                "join",
                "length",
                "multiply",
                "negate",
                "parse_decimal",
                "quotient",
                "remainder",
                "shift_left",
                "shift_right",
                "slice",
                "split_exact",
                "subtract",
                "utf8_decode",
                "utf8_encode",
            ])
            .into_iter()
            .map(str::to_owned)
            .collect();
            assert_eq!(
                found, expected,
                "every closed portable primitive is exercised"
            );
            let lean = project.build_ok();
            let generated = std::fs::read_to_string(
                project
                    .build_dir(&lean.build_id.expect("build id"))
                    .join("modules/SemanticFixture/Portable.lean")
                    .as_std_path(),
            )
            .expect("portable generated Lean");
            assert!(generated.contains("public def isZeroInt64"));
            assert!(generated.contains("\"portable ✓\""));

            let mismatched = support::semantic_project();
            mismatched.edit(
                "src/Portable.lex.tex",
                "\"representation\":\"int64\",\"value\":\"0\"",
                "\"representation\":\"uint64\",\"value\":\"0\"",
            );
            let error = mismatched.check_err();
            assert!(
                error
                    .to_string()
                    .contains("has type UInt64, expected Int64"),
                "unexpected mismatch diagnostic: {error}"
            );
        }
        "SM-19" => {
            let project = support::semantic_project();
            let built = project.build_ok();
            let root = project.build_dir(&built.build_id.expect("build id"));
            let lean = std::fs::read_to_string(
                root.join("modules/SemanticFixture/Portable.lean")
                    .as_std_path(),
            )
            .expect("portable generated Lean");
            for needle in [
                "public class Fixed",
                "public def checkedAdd",
                "public def utf8Decode",
                "public def parseDecimal",
                "public def checkedAddInt64",
            ] {
                assert!(lean.contains(needle), "generated Lean is missing {needle}");
            }
            let _ = support::verify_ok_backed("SM-19", &project);
            if support::lean_backed("SM-19") {
                let evaluations = r#"open SemanticFixture.Portable
#eval subtractInt 5 8 == -3
#eval multiplyInt (-7) 6 == -42
#eval quotientInt (-7) 2 99 == -3
#eval quotientInt 1 0 99 == 99
#eval remainderInt (-7) 2 99 == -1
#eval negateInt 42 == -42
#eval isZeroInt64 0
#eval !(isZeroInt64 1)
#eval convertInt64 42 == some 42
#eval checkedAddInt64 40 2 == some 42
#eval checkedSubtractInt64 40 2 == some 38
#eval checkedMultiplyInt64 6 7 == some 42
#eval checkedNegateInt64 42 == some (-42)
#eval checkedQuotientInt64 (-7) 2 == some (-3)
#eval andUInt64 12 10 == 8
#eval orUInt64 12 10 == 14
#eval xorUInt64 12 10 == 6
#eval notUInt64 0 == 18446744073709551615
#eval shiftUInt64 1 3 == some 8
#eval shiftRightUInt64 8 3 == some 1
#eval appendBytes (ByteArray.mk #[1]) (ByteArray.mk #[2]) == ByteArray.mk #[1, 2]
#eval byteLength (ByteArray.mk #[1, 2]) == 2
#eval byteAt (ByteArray.mk #[1, 2]) 1 == some 2
#eval sliceBytes (ByteArray.mk #[1, 2, 3]) 1 2 == some (ByteArray.mk #[2, 3])
#eval encodeUtf8 "A" == ByteArray.mk #[65]
#eval decodeUtf8 (ByteArray.mk #[65]) == some "A"
#eval compareByteStrings (ByteArray.mk #[1]) (ByteArray.mk #[2]) == Ordering.lt
#eval splitBounded "a::b" "::" 2 == some ["a", "b"]
#eval joinStrings ["a", "b"] "::" == "a::b"
#eval parseInt64 "-42" == some (-42)
#eval formatInt64 (-42) == "-42"
#eval checkedAddInt64 9223372036854775807 1 == none
#eval checkedQuotientInt64 (-9223372036854775808) (-1) == none
#eval shiftUInt64 1 64 == none
#eval byteAt (ByteArray.mk #[1, 2]) 2 == none
#eval sliceBytes (ByteArray.mk #[1, 2, 3]) 2 2 == none
#eval decodeUtf8 (ByteArray.mk #[255]) == none
#eval splitBounded "a::b" "::" 1 == none
#eval parseInt64 "01" == none
"#;
                let directory = tempfile::Builder::new()
                    .prefix("lexlean-portable-runtime-")
                    .tempdir()
                    .expect("runtime fixture tempdir");
                let path = directory.path().join("PortableRuntime.lean");
                std::fs::write(&path, format!("{lean}\n{evaluations}"))
                    .expect("write runtime evaluation module");
                let binary = support::real_elan_home()
                    .join("toolchains")
                    .join(support::mangled_toolchain_name())
                    .join("bin")
                    .join(if cfg!(windows) { "lean.exe" } else { "lean" });
                let output = Command::new(binary)
                    .arg(&path)
                    .current_dir(directory.path())
                    .env("LEAN_PATH", "")
                    .output()
                    .expect("pinned Lean evaluates portable runtime vectors");
                assert!(
                    output.status.success(),
                    "portable runtime evaluation failed: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let stdout = String::from_utf8(output.stdout).expect("Lean output is UTF-8");
                let expected = evaluations
                    .lines()
                    .filter(|line| line.starts_with("#eval"))
                    .count();
                assert_eq!(stdout.lines().count(), expected);
                assert!(
                    stdout.lines().all(|line| line == "true"),
                    "portable runtime vector failed: {stdout}"
                );
            }
        }
        "SM-20" => {
            let range = support::semantic_project();
            range.edit(
                "src/Portable.lex.tex",
                "\"representation\":\"uint8\",\"value\":\"255\"",
                "\"representation\":\"uint8\",\"value\":\"256\"",
            );
            let error = range.check_err();
            assert!(error.to_string().contains("outside UInt8"));

            let bytes = support::semantic_project();
            bytes.edit(
                "src/Portable.lex.tex",
                "\"hex\":\"aabb7fff\"",
                "\"hex\":\"AAbb7fff\"",
            );
            let error = bytes.check_err();
            assert!(error.to_string().contains("lowercase hexadecimal"));

            let typing = support::semantic_project();
            typing.edit(
                "src/Portable.lex.tex",
                "\"operation\":\"checked_add\",\"result\":{\"kind\":\"option\",\"value\":{\"kind\":\"int64\"}}",
                "\"operation\":\"checked_add\",\"result\":{\"kind\":\"int64\"}",
            );
            let error = typing.check_err();
            assert!(error.to_string().contains("result is Int64"));
        }
        "SM-21" => {
            let project = support::semantic_project();
            project.check_ok();
            let bad = support::semantic_project();
            bad.edit(
                "src/PortableRecursion.lex.tex",
                "{\"kind\":\"var\",\"name\":\"tail\"}],\"function\":{\"name\":\"byteListLength\"}",
                "{\"kind\":\"var\",\"name\":\"bytes\"}],\"function\":{\"name\":\"byteListLength\"}",
            );
            let error = bad.check_err();
            assert!(error.to_string().contains("structurally smaller"));

            let missing_option_branch = support::semantic_project();
            missing_option_branch.edit(
                "src/PortableRecursion.lex.tex",
                ",{\"binders\":[\"payload\"],\"body\":{\"kind\":\"bool\",\"value\":true},\"constructor\":{\"name\":\"PortableOptionByte.some\"}}",
                "",
            );
            let error = missing_option_branch.check_err();
            assert!(error.to_string().contains("exhaustive"));

            let missing_result_branch = support::semantic_project();
            missing_result_branch.edit(
                "src/PortableRecursion.lex.tex",
                ",{\"binders\":[\"payload\"],\"body\":{\"kind\":\"bool\",\"value\":true},\"constructor\":{\"name\":\"PortableResultByte.ok\"}}",
                "",
            );
            let error = missing_result_branch.check_err();
            assert!(error.to_string().contains("exhaustive"));
        }
        "SM-22" => {
            use lexlean::{
                SnapshotInteger as I, SnapshotPrimitive as O, SnapshotTerm as Term,
                SnapshotType as T,
            };

            let integers = [
                I::Int,
                I::Int8,
                I::Int16,
                I::Int32,
                I::Int64,
                I::UInt8,
                I::UInt16,
                I::UInt32,
                I::UInt64,
            ];
            let primitives = [
                O::Subtract,
                O::Multiply,
                O::Quotient,
                O::Remainder,
                O::Negate,
                O::CheckedConvert,
                O::CheckedAdd,
                O::CheckedSubtract,
                O::CheckedMultiply,
                O::CheckedNegate,
                O::CheckedQuotient,
                O::BitAnd,
                O::BitOr,
                O::BitXor,
                O::BitNot,
                O::ShiftLeft,
                O::ShiftRight,
                O::Append,
                O::Length,
                O::Index,
                O::Slice,
                O::Utf8Encode,
                O::Utf8Decode,
                O::CompareBytes,
                O::Equal,
                O::SplitExact,
                O::Join,
                O::ParseDecimal,
                O::FormatDecimal,
            ];
            let types = vec![
                T::Int,
                T::Int8,
                T::Int16,
                T::Int32,
                T::Int64,
                T::UInt8,
                T::UInt16,
                T::UInt32,
                T::UInt64,
                T::String,
                T::Bytes,
                T::Ordering,
                T::Option {
                    value: Box::new(T::Int64),
                },
                T::Result {
                    ok: Box::new(T::Int64),
                    error: Box::new(T::String),
                },
            ];
            let terms = [
                Term::Integer {
                    representation: I::Int64,
                    value: "-1".to_owned(),
                },
                Term::String {
                    value: "portable".to_owned(),
                },
                Term::Bytes {
                    hex: "00ff".to_owned(),
                },
                Term::Primitive {
                    operation: O::CheckedAdd,
                    arguments: Vec::new(),
                    result: T::Option {
                        value: Box::new(T::Int64),
                    },
                },
            ];
            assert_eq!(integers.len(), 9, "downstream integer DTO variants");
            assert_eq!(primitives.len(), 29, "downstream primitive DTO variants");
            assert_eq!(types.len(), 14, "downstream portable type DTO variants");
            assert_eq!(terms.len(), 4, "downstream portable term DTO variants");

            let bounded = support::semantic_project();
            bounded.edit(
                "lexlean.toml",
                "max_ir_nodes = 2000000",
                "max_ir_nodes = 100",
            );
            bounded.relock();
            let error = bounded.check_fails_with("LLS8002");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains("max_ir_nodes exceeded")),
                "portable semantic terms are recursively charged to max_ir_nodes"
            );

            let left = support::semantic_project();
            let right = support::semantic_project();
            let snapshot = |project: &P| {
                project
                    .engine()
                    .snapshot(lexlean::CheckRequest {
                        selection: lexlean::Selection::Entrypoints,
                    })
                    .expect("portable snapshot")
            };
            let first = snapshot(&left);
            let second = snapshot(&right);
            assert_eq!(first.canonical_bytes(), second.canonical_bytes());
            assert_eq!(first.snapshot_id(), second.snapshot_id());
            let value: serde_json::Value =
                serde_json::from_slice(&first.canonical_bytes()).expect("snapshot JSON");
            support::assert_schema("semantic-snapshot", "portable snapshot", &value);
            let bytes = String::from_utf8(first.canonical_bytes()).expect("utf8");
            assert!(!bytes.contains(left.root.as_str()));
            assert!(!bytes.contains("public def"));
            assert!(!bytes.contains("generated Rust"));
            assert!(bytes.contains("\"axioms\":[\"Quot.sound\",\"propext\"]"));
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
