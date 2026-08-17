//! The `lean-backend` suite: LN-01..LN-12.

use lexlean::verify::source_audit::{audit, lex, LeanToken};

use crate::support::{self, P};

/// The §29.3 generated Lean of the literal example, byte for byte.
const EXAMPLE_LEAN: &str = "module\npublic import Init\nset_option autoImplicit false\nnamespace LexLeanExample.Main\n\npublic theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  rfl\n\nend LexLeanExample.Main\n";

fn example_lean() -> String {
    support::lean_text(&support::rendered(&P::example()), "Main")
}

fn lean_of(module: &str) -> String {
    let project = P::example();
    project.write("src/Main.lex.tex", module);
    project.check_ok();
    support::lean_text(&support::rendered(&project), "Main")
}

fn theorem_module(statement: &str, proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{main-goal}}\n\\noaxioms\n{statement}\n\\begin{{proof}}\n{proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

/// The proof body (after `:= by`) of a one-theorem generated file.
fn proof_body(lean: &str) -> &str {
    lean.split_once(":= by\n")
        .expect("a tactic proof")
        .1
        .split_once("\nend ")
        .expect("the end")
        .0
}

pub(crate) fn run(id: &str) {
    match id {
        // §18.1: the exact file structure, in order, byte for byte for the
        // literal example and for a sectioned module.
        "LN-01" => {
            assert_eq!(example_lean(), EXAMPLE_LEAN, "§29.3 bytes");
            let project = P::example();
            project.write("src/Main.lex.tex", support::SECTIONS_MODULE);
            project.check_ok();
            assert_eq!(
                support::lean_text(&support::rendered(&project), "Main"),
                support::SECTIONS_LEAN,
                "sections do not appear in Lean; only the used parameter does"
            );
        }
        // §18.3: sorted unique imports; fully qualified externals; no open;
        // externals reached through defined values and case constructors
        // import their modules too.
        "LN-02" => {
            let lean = example_lean();
            let imports: Vec<&str> = lean
                .lines()
                .filter(|line| line.starts_with("public import "))
                .collect();
            let mut sorted = imports.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(imports, sorted, "imports are sorted and deduplicated");
            assert_eq!(imports, vec!["public import Init"]);
            assert!(
                lean.contains("Nat.add"),
                "external globals are fully qualified: {lean}"
            );
            assert!(!lean.contains("open "), "no open statements: {lean}");

            let project = support::ext_project(support::DEFINED_MODULE);
            let checked = support::checked_project(&project);
            let externals = lexlean::backend::lean::document_externals(
                &checked.modules["Main"].document,
                &checked.closure,
            );
            let mut names: Vec<&str> = externals
                .values()
                .map(|external| external.lean_name.as_str())
                .collect();
            names.sort_unstable();
            assert_eq!(
                names,
                vec!["Nat.succ", "Nat.zero"],
                "constants inside the inlined defined value are collected"
            );
            let checked = support::checked_project(&{
                let project = P::example();
                project.write("src/Main.lex.tex", support::PROOF_FORMS_MODULE);
                project
            });
            let externals = lexlean::backend::lean::document_externals(
                &checked.modules["Main"].document,
                &checked.closure,
            );
            assert!(
                externals.contains_key("lexlean.std.nat::succ")
                    && externals.contains_key("lexlean.std.nat::zero"),
                "case constructors are collected: {:?}",
                externals.keys().collect::<Vec<_>>()
            );
        }
        // §18.2: no comments, strings, or copied prose.
        "LN-03" => {
            for lean in [
                example_lean(),
                support::lean_text(&support::rendered(&support::defs_project()), "Main"),
            ] {
                assert!(!lean.contains("--"), "no line comments: {lean}");
                assert!(!lean.contains("/-"), "no block comments: {lean}");
                assert!(!lean.contains('"'), "no string literals: {lean}");
                assert!(!lean.contains("natural number"), "no copied prose: {lean}");
                audit(&lean, false).expect("the generated-source audit accepts it");
            }
        }
        // §18.2: none of the forbidden declaration forms. The spellings are
        // assembled from halves so this file passes its own audit.
        "LN-04" => {
            let forbidden = [
                format!("sor{}", "ry"),
                format!("adm{}", "it"),
                format!("axi{} ", "om"),
                format!("opa{} ", "que"),
                format!("{}safe", "un"),
                format!("native_{}", "decide"),
            ];
            for lean in [
                example_lean(),
                support::lean_text(&support::rendered(&support::defs_project()), "Main"),
                support::PROOF_FORMS_LEAN.to_owned(),
            ] {
                for token in &forbidden {
                    assert!(
                        !lean.contains(token.as_str()),
                        "generated Lean contains `{token}`: {lean}"
                    );
                }
                audit(&lean, false).expect("audit accepts");
            }
        }
        // §18.4, §18.7: every pinned lowering form has exact bytes and
        // verifies with real Lean; unique existence lowers to its
        // expansion; missing lowering is a hard error.
        "LN-05" => {
            let project = P::example();
            project.write("src/Main.lex.tex", support::PROOF_FORMS_MODULE);
            project.check_ok();
            assert_eq!(
                support::lean_text(&support::rendered(&project), "Main"),
                support::PROOF_FORMS_LEAN,
                "cases, right, induction, intro, apply with premises, and calc"
            );
            support::verify_ok(&project);

            // Witness, left, have, rewrite, simp only.
            assert_eq!(
                proof_body(&lean_of(&theorem_module(
                    "There exists a natural number \\(k\\) such that \\(k + 0 = k\\).",
                    "Use \\(0\\) as the witness.\nClose the goal by reflexivity.",
                ))),
                "  refine ⟨(0 : Nat), ?_⟩\n  rfl\n"
            );
            assert_eq!(
                proof_body(&lean_of(&theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\) or \\(n = 1\\).",
                    "Select the left alternative.\nClose the goal by reflexivity.",
                ))),
                "  left\n  rfl\n"
            );
            assert_eq!(
                proof_body(&lean_of(&theorem_module(
                    "For every natural number \\(n\\), \\(n + 0 = n\\).",
                    "\\begin{have}{h}\n\\(n + 0 = n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{have}\nClose the goal with \\(h\\).",
                ))),
                "  have llh0 : Eq (Nat.add llv0 0) llv0 := by\n    rfl\n  exact llh0\n"
            );
            let two = |proof: &str| {
                format!(
                    "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{first}}\n\\noaxioms\nFor every natural number \\(m\\), \\(m + 0 = m\\).\n\\begin{{proof}}\nClose the goal by reflexivity.\n\\end{{proof}}\n\\end{{theorem}}\n\n\\begin{{theorem}}{{second}}\n\\noaxioms\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\begin{{proof}}\n{proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
                )
            };
            let rewrite = lean_of(&two(
                "\\begin{rewrite}{goal}\n\\forward{\\reference{Main::first}}\n\\end{rewrite}\nClose the goal by reflexivity.",
            ));
            assert!(
                rewrite.ends_with("public theorem second (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by\n  rw [LexLeanExample.Main.first]\n  rfl\n\nend LexLeanExample.Main\n"),
                "rw lowering: {rewrite}"
            );
            let simp = lean_of(&two(
                "\\begin{simplify}{goal}\n\\rule{\\reference{Main::first}}\n\\end{simplify}\nClose the goal by reflexivity.",
            ));
            assert!(
                simp.ends_with(
                    "  simp only [LexLeanExample.Main.first]\n  rfl\n\nend LexLeanExample.Main\n"
                ),
                "simp only lowering: {simp}"
            );

            // Unique existence: the documented expansion, verified end to
            // end; the residual goal after the witness is the conjunction.
            let unique = support::ext_project(support::UNIQUE_MODULE);
            unique.check_ok();
            assert_eq!(
                support::lean_text(&support::rendered(&unique), "Main"),
                support::UNIQUE_LEAN
            );
            support::verify_ok(&unique);

            // Numerals ascribe outside monomorphic parameter positions
            // (`(1 : Nat)` under `Eq`, bare under `Nat.add`).
            assert!(
                support::PROOF_FORMS_LEAN
                    .contains("Or (Eq llv0 (1 : Nat)) (Eq (Nat.add llv0 0) llv0)"),
                "numeral ascription"
            );

            // The ascription is what the expected type is *defined as*, in
            // every module of the project: a document type definition
            // declared in an imported module unfolds exactly as one
            // declared here (§17.7). Lean's `OfNat` instances live on the
            // underlying type, so `(0 : Alias.count)` could never elaborate.
            let alias = support::imported_alias_project();
            alias.check_ok();
            let alias_main = support::lean_text(&support::rendered(&alias), "Main");
            assert!(
                alias_main.contains(
                    "public theorem alias_numeral (llv0 : LexLeanExample.Alias.count) : (Eq llv0 (0 : Nat)) \u{2192} Eq llv0 (0 : Nat) := by\n"
                ),
                "an imported alias ascribes at what it is defined as: {alias_main}"
            );
            assert!(
                !alias_main.contains("(0 : LexLeanExample.Alias.count)"),
                "the alias itself is never the ascription: {alias_main}"
            );
            support::verify_ok(&alias);

            // A defined value reaching Lean constants inlines them, and its
            // constants are imported and probed.
            let defined = support::ext_project(support::DEFINED_MODULE);
            defined.check_ok();
            assert_eq!(
                support::lean_text(&support::rendered(&defined), "Main"),
                support::DEFINED_LEAN
            );
            support::verify_ok(&defined);

            // Missing lowering is a hard error: the calculation lowering
            // exists only for the equality descriptor, and a non-equality
            // relation is rejected before rendering.
            let project = P::example();
            project.write(
                "src/Main.lex.tex",
                &theorem_module(
                    "\\(0 + 0 = 0\\).",
                    "\\begin{calculate}\n\\start{0 + 0}\n\\step{lexlean.std.nat::le}{0}{\\reference{Main::main-goal}}\n\\end{calculate}",
                ),
            );
            let error = project.check_err();
            assert!(
                !error.diagnostics.is_empty(),
                "a non-equality calculation relation is a hard error"
            );
        }
        // §18.5: leading universals become parameters, source-mapped per
        // binder; section parameters close under type dependencies.
        "LN-06" => {
            let build = support::rendered(&P::example());
            let module = &build.modules[0];
            assert!(
                module.lean_text.contains("(llv0 : Nat)"),
                "the leading universal is a declaration parameter: {}",
                module.lean_text
            );
            assert!(
                !module.lean_text.contains('\u{2200}'),
                "no residual quantifier for the peeled binder"
            );
            let at = module.lean_text.find("llv0").expect("the parameter");
            let mapping = module.map.remap(0, at).expect("the parameter is mapped");
            assert_eq!(mapping.role, lexlean::artifact::source_map::MapRole::Binder);
            let normalized = &support::checked_project(&P::example()).modules["Main"].normalized;
            let (start, end) = mapping.src_range.expect("a source range");
            assert_eq!(
                &normalized[start..end],
                "n",
                "the parameter maps to its binder"
            );
            assert!(
                module
                    .coverage
                    .lean
                    .iter()
                    .any(|row| row.byte_start <= at && at < row.byte_end),
                "the parameter token has a coverage origin"
            );

            let dependent = support::ext_project(support::DEPENDENT_MODULE);
            dependent.check_ok();
            assert_eq!(
                support::lean_text(&support::rendered(&dependent), "Main"),
                support::DEPENDENT_LEAN,
                "an unused parameter mentioned by a used parameter's type is included"
            );
            support::verify_ok(&dependent);
        }
        // §18.6: definitions are always def, byte-exact, and verify.
        "LN-07" => {
            let project = support::defs_project();
            let lean = support::lean_text(&support::rendered(&project), "Main");
            assert_eq!(lean, support::DEFS_LEAN);
            for forbidden in [
                "abbrev",
                "instance ",
                "structure ",
                "inductive ",
                "theorem count",
            ] {
                assert!(
                    !lean.contains(forbidden),
                    "no alternate declaration forms: {lean}"
                );
            }
            support::verify_ok(&project);

            // §18.4: a numeral whose expected type is a document type
            // definition ascribes the type that definition unfolds to.
            // Lean synthesizes `OfNat` against the type as written, and a
            // `def count : Type := Nat` carries no instance, so `(0 : count)`
            // and a bare `0` in that position are both rejected by the
            // pinned toolchain — the emitted `(0 : Nat)` is not.
            let aliased = support::alias_numeral_project();
            let lean = support::lean_text(&support::rendered(&aliased), "Main");
            assert!(
                lean.contains("tally (0 : Nat)"),
                "the numeral ascribes the unfolded type: {lean}"
            );
            assert!(
                !lean.contains("(0 : LexLeanExample.Main.count)") && !lean.contains("tally 0"),
                "neither the alias nor a bare numeral reaches Lean: {lean}"
            );
            assert!(
                lean.contains("def count : Type :=") && lean.contains("def tally"),
                "the alias itself is still emitted as a def naming the alias: {lean}"
            );
            support::verify_ok(&aliased);

            // §13.6, §18.4: a saturated application of a defined lexicon
            // value prints as its beta-reduct — the value's meaning, the
            // same term the elaborator read (§17.6) — not a lambda applied
            // in place. `lexlean.std.nat::ne` is `fun a b => Not (Eq a b)`.
            let defined = P::example();
            defined.edit(
                "src/Main.lex.tex",
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "For every natural number \\(n\\), not \\(n + 0 ≠ n\\).",
            );
            defined.edit(
                "src/Main.lex.tex",
                "Close the goal by reflexivity.",
                "Assume \\(h\\).\nApply \\(h\\).\nClose the goal by reflexivity.",
            );
            let lean = support::lean_text(&support::rendered(&defined), "Main");
            assert!(
                lean.contains("Not (Not (Eq (Nat.add llv0 0) llv0))"),
                "the defined value is beta-reduced: {lean}"
            );
            assert!(
                !lean.contains("fun (x"),
                "no lambda is applied in place: {lean}"
            );
            support::verify_ok(&defined);
        }
        // §18.7: proof lowering uses only the fixed pinned forms.
        "LN-08" => {
            assert_eq!(proof_body(EXAMPLE_LEAN), "  rfl\n");
            let pinned = [
                "intro",
                "exact",
                "apply",
                "rfl",
                "refine",
                "constructor",
                "left",
                "right",
                "have",
                "rw",
                "simp",
                "only",
                "cases",
                "induction",
                "with",
                "calc",
                "by",
                "at",
            ];
            for lean in [support::PROOF_FORMS_LEAN, support::UNIQUE_LEAN] {
                for declaration in lean.split("public theorem ").skip(1) {
                    let body = declaration
                        .split_once(":= by\n")
                        .expect("a tactic proof")
                        .1
                        .split("\n\n")
                        .next()
                        .expect("the body");
                    for line in body.lines().filter(|line| !line.trim().is_empty()) {
                        let head = line.trim_start();
                        assert!(
                            pinned.iter().any(|form| head.starts_with(form))
                                || head.starts_with('|')
                                || head.starts_with('_'),
                            "every tactic line opens with a pinned form: `{line}`"
                        );
                    }
                }
            }
        }
        // §18.1: byte determinism, LF, final LF, fixed indentation.
        "LN-09" => {
            let first = example_lean();
            let second = example_lean();
            assert_eq!(first, second, "byte-deterministic");
            assert!(first.ends_with('\n'), "one final LF");
            assert!(
                !first.contains('\r') && !first.contains('\t'),
                "LF and spaces only"
            );
            for lean in [first.as_str(), support::PROOF_FORMS_LEAN] {
                for line in lean.lines() {
                    let indent = line.len() - line.trim_start_matches(' ').len();
                    assert_eq!(indent % 2, 0, "two-space indentation steps: {line:?}");
                }
            }
        }
        // §18.2, I13: every non-whitespace Lean token has a mapping.
        "LN-10" => {
            let build = support::rendered(&P::example());
            let module = &build.modules[0];
            let text = module.lean_text.as_bytes();
            let rows = &module.coverage.lean;
            for (index, byte) in text.iter().enumerate() {
                if byte.is_ascii_whitespace() {
                    continue;
                }
                let covering = rows
                    .iter()
                    .filter(|row| row.byte_start <= index && index < row.byte_end)
                    .count();
                assert_eq!(
                    covering,
                    1,
                    "lean byte {index} ({:?}) is covered exactly once, found {covering}",
                    module.lean_text[index..].chars().next()
                );
                assert!(
                    module.map.remap(0, index).is_some(),
                    "lean byte {index} has a mapping"
                );
            }

            // An inlined defined lexicon value (§13.6) is a whole term, not
            // an identifier: `two` inlines as `(Nat.succ (Nat.succ
            // Nat.zero))`. It is covered token by token, so a Lean
            // diagnostic inside it remaps to a token-sized range rather
            // than to the entire inlined value (§20.3, §20.4).
            let inlined = support::rendered(&support::ext_project(support::DEFINED_MODULE));
            let module = &inlined.modules[0];
            let rows: Vec<&lexlean::source::coverage::OutputRow> = module
                .coverage
                .lean
                .iter()
                .filter(|row| {
                    matches!(
                        &row.origin,
                        lexlean::source::coverage::Origin::Form { package, entry, .. }
                            if package == "test.ext" && entry == "two"
                    )
                })
                .collect();
            let spelled: Vec<&str> = rows
                .iter()
                .map(|row| &module.lean_text[row.byte_start..row.byte_end])
                .collect();
            assert_eq!(
                spelled,
                vec![
                    "(", "Nat.succ", "(", "Nat.succ", "Nat.zero", ")", ")", "(", "Nat.succ", "(",
                    "Nat.succ", "Nat.zero", ")", ")"
                ],
                "both occurrences of the inlined value are covered token by token: {}",
                module.lean_text
            );
            for row in rows {
                let mapping = module
                    .map
                    .remap(0, row.byte_start)
                    .expect("every inlined token has a mapping");
                assert!(
                    mapping.gen_end - mapping.gen_start <= row.byte_end - row.byte_start,
                    "the smallest enclosing mapping is the token, not the whole inlined value"
                );
            }
        }
        // §18.2: the generated-source audit is a token lexer.
        "LN-11" => {
            // Token classes.
            assert_eq!(
                lex("Foo.bar x' «a b».c #print 12 0x1F \"s\" 'c' -- hi\n/- a /- b -/ c -/ →")
                    .expect("lexes"),
                vec![
                    LeanToken::Ident(vec!["Foo".to_owned(), "bar".to_owned()]),
                    LeanToken::Ident(vec!["x'".to_owned()]),
                    LeanToken::Ident(vec!["«a b»".to_owned(), "c".to_owned()]),
                    LeanToken::Command("#print".to_owned()),
                    LeanToken::Numeral("12".to_owned()),
                    LeanToken::Numeral("0x1F".to_owned()),
                    LeanToken::StringLit("\"s\"".to_owned()),
                    LeanToken::CharLit("'c'".to_owned()),
                    LeanToken::Comment("-- hi".to_owned()),
                    LeanToken::Comment("/- a /- b -/ c -/".to_owned()),
                    LeanToken::Symbol("→".to_owned()),
                ]
            );
            assert!(lex("/- open").is_err(), "unterminated block comment");
            assert!(lex("\"open").is_err(), "unterminated string");
            // Rejections, one per class; spellings are assembled from halves
            // so this file passes its own audit.
            let sorry = format!("sor{}", "ry");
            let rejected = [
                format!("theorem t : True := {sorry}"),
                format!("theorem t : True := Foo.{sorry}"),
                format!("theorem t : True := by ad{}", "mit"),
                format!("axi{} a : True", "om"),
                format!("opa{} def x : Nat := 0", "que"),
                format!("un{} def x : Nat := 0", "safe"),
                format!("example : True := by native_{}", "decide"),
                "-- a comment".to_owned(),
                "/- a comment -/".to_owned(),
                "/-- doc -/ def x := 0".to_owned(),
                "def s := \"text\"".to_owned(),
                "def c := 'c'".to_owned(),
                format!("#{} 1", "eval"),
                format!("#{} Nat", "print"),
                format!("#{} Nat", "check"),
                format!("#{} 1", "reduce"),
                format!("#{}", "exit"),
                "def main : IO Unit := pure ()".to_owned(),
                "def x := IO.println".to_owned(),
            ];
            for text in &rejected {
                assert!(audit(text, false).is_err(), "`{text}` is rejected");
            }
            // Accepted: identifier fragments and the audit module's one
            // permitted command.
            assert!(audit("def sorrowful : Nat := 0", false).is_ok());
            assert!(audit("def admittedly : Nat := 0", false).is_ok());
            assert!(audit("def x := Nat.axiomatic", false).is_ok());
            assert!(audit("#print axioms Foo.bar", true).is_ok());
            assert!(audit("#print axioms Foo.bar", false).is_err());
            assert!(audit(&format!("#{} Foo", "print"), true).is_err());
            for lean in [
                support::PROOF_FORMS_LEAN,
                support::UNIQUE_LEAN,
                support::DEFS_LEAN,
            ] {
                audit(lean, false).expect("generated modules pass");
            }
            // The verified fixture published its audited probe and audit
            // modules; both pass the same lexer.
            let fixture = support::verified();
            for directory in ["probe", "audit"] {
                let dir = fixture.outcome.root.join(directory);
                let lean = std::fs::read_dir(dir.as_std_path())
                    .expect("dir")
                    .flatten()
                    .find(|entry| entry.path().extension().is_some_and(|ext| ext == "lean"))
                    .expect("a lean file");
                let text = std::fs::read_to_string(lean.path()).expect("read");
                audit(&text, directory == "audit").expect("published generated source passes");
            }
        }
        // §18.3: paths and module names mirror the configured prefix.
        "LN-12" => {
            let project = P::example();
            let build = support::rendered(&project);
            let module = &build.modules[0];
            assert_eq!(module.lean_module, "LexLeanExample.Main");
            assert_eq!(module.lean_path, "modules/LexLeanExample/Main.lean");
            assert!(module.lean_text.contains("namespace LexLeanExample.Main"));

            let renamed = P::example();
            renamed.edit(
                "lexlean.toml",
                "module_prefix = \"LexLeanExample\"",
                "module_prefix = \"Other\"",
            );
            renamed.relock();
            let build = support::rendered(&renamed);
            assert_eq!(build.modules[0].lean_path, "modules/Other/Main.lean");
            assert!(build.modules[0].lean_text.contains("namespace Other.Main"));
        }
        other => panic!("no lean-backend case is wired for {other}"),
    }
}
