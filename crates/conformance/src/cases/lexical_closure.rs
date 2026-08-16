//! The `lexical-closure` suite: LX-01..LX-14.

use lexlean::source::coverage::Origin;

use crate::support::{self, P};

fn write_bytes(project: &P, relative: &str, bytes: &[u8]) {
    std::fs::write(project.root.join(relative).as_std_path(), bytes).expect("write");
}

/// The example source with one replacement applied.
fn mutated(from: &str, to: &str) -> P {
    let project = P::example();
    project.edit("src/Main.lex.tex", from, to);
    project
}

/// Both duplicate-`nzz` packages, glossary rows in the given order.
fn ambiguous_project(order: [&str; 2]) -> P {
    let project = P::example();
    project.add_package(
        "lexicons/test-dupa",
        "test.dupa",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        &[
            ("nzz.toml", &support::nzz_entry("Nat.le_refl")),
            ("z.toml", Z_ENTRY_A),
        ],
    );
    project.add_package(
        "lexicons/test-dupb",
        "test.dupb",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        &[("nzz.toml", &support::nzz_entry("Nat.ge_refl"))],
    );
    project.write("src/Main.lex.tex", &support::nzz_module(&order));
    project.relock();
    project
}

const Z_ENTRY_A: &str = r#"spec = "lexlean/entry/1"
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

pub(crate) fn run(id: &str) {
    match id {
        // §12.1: UTF-8, LF, final LF, forbidden scalars.
        "LX-01" => {
            let invalid = P::example();
            write_bytes(
                &invalid,
                "src/Main.lex.tex",
                b"\\begin{lexlean}{Main}\n\xFF\n",
            );
            invalid.check_fails_with("LLL1001");

            let nul = P::example();
            nul.edit("src/Main.lex.tex", "\\title{", "\u{0}\\title{");
            nul.check_fails_with("LLL1001");

            let unterminated = P::example();
            let text = unterminated.read("src/Main.lex.tex");
            write_bytes(
                &unterminated,
                "src/Main.lex.tex",
                text.trim_end().as_bytes(),
            );
            unterminated.check_fails_with("LLL1001");

            let bom = P::example();
            let text = bom.read("src/Main.lex.tex");
            write_bytes(
                &bom,
                "src/Main.lex.tex",
                &[b"\xEF\xBB\xBF".to_vec(), text.into_bytes()].concat(),
            );
            bom.check_fails_with("LLL1001");
        }
        // §12.1: non-NFC is diagnosed; formatting rewrites to NFC.
        "LX-02" => {
            let project = mutated(
                "Natural number addition",
                "Natural number additio\u{6E}\u{0303}",
            );
            project.check_fails_with("LLL1003");

            let normalized = lexlean::source::normalize::normalize(
                "src/Main.lex.tex",
                "\\title{additio\u{6E}\u{0303}}\n".as_bytes(),
                true,
            )
            .expect("fmt-mode normalization rewrites NFC");
            assert!(
                normalized.text.contains('\u{00F1}'),
                "the formatter output is NFC-composed"
            );
        }
        // §12.1: percent, tabs, trailing spaces, non-ASCII whitespace.
        "LX-03" => {
            mutated("For every", "% comment\nFor every").check_fails_with("LLL1002");
            mutated("For every", "\tFor every").check_fails_with("LLL1002");
            mutated("\\(n + 0 = n\\).\n", "\\(n + 0 = n\\). \n").check_fails_with("LLL1001");
            mutated("For every", "For\u{00A0}every").check_fails_with("LLL1001");
        }
        // §12.2: the exact atom classes with exact spans.
        "LX-04" => {
            use lexlean::source::atom::AtomClass;
            let text = "\\begin{lexlean}{Main}\ntext 12 + \u{2115}\n";
            let atoms = lexlean::source::scan::scan("m.lex.tex", text, 1_000).expect("scan");
            let classes: Vec<(AtomClass, &str)> = atoms
                .iter()
                .map(|atom| (atom.class, &text[atom.byte_start..atom.byte_end]))
                .collect();
            let expected: Vec<(AtomClass, &str)> = vec![
                (AtomClass::Control, "\\begin"),
                (AtomClass::Delimiter, "{"),
                (AtomClass::Word, "lexlean"),
                (AtomClass::Delimiter, "}"),
                (AtomClass::Delimiter, "{"),
                (AtomClass::Word, "Main"),
                (AtomClass::Delimiter, "}"),
                (AtomClass::Whitespace, "\n"),
                (AtomClass::Word, "text"),
                (AtomClass::Whitespace, " "),
                (AtomClass::Numeral, "12"),
                (AtomClass::Whitespace, " "),
                (AtomClass::AsciiSymbol, "+"),
                (AtomClass::Whitespace, " "),
                (AtomClass::UnicodeSymbol, "\u{2115}"),
                (AtomClass::Whitespace, "\n"),
            ];
            assert_eq!(classes, expected, "§12.2 atom classes and spans");
            // Spans are exact and contiguous.
            let mut cursor = 0usize;
            for atom in &atoms {
                assert_eq!(atom.byte_start, cursor, "atoms are contiguous");
                cursor = atom.byte_end;
            }
            assert_eq!(cursor, text.len(), "atoms cover the whole file");
        }
        // §12.3: core syntax is glossary-covered, not TeX-trusted.
        "LX-05" => {
            let project = P::example();
            let checked = support::checked_project(&project);
            let module = &checked.modules["Main"];
            let begin_atom = module
                .atoms
                .iter()
                .find(|atom| &module.normalized[atom.byte_start..atom.byte_end] == "\\begin")
                .expect("the module has \\begin");
            let row = module
                .coverage_source
                .iter()
                .find(|row| row.byte_start == begin_atom.byte_start)
                .expect("\\begin is covered");
            match &row.binding {
                Origin::Structural { package, entry } => {
                    assert_eq!(package, "lexlean.core");
                    assert_eq!(entry, "begin");
                }
                other => {
                    panic!("\\begin must be covered by a core structural entry, found {other:?}")
                }
            }
            let brace = module
                .atoms
                .iter()
                .find(|atom| &module.normalized[atom.byte_start..atom.byte_end] == "{")
                .expect("a brace");
            assert!(
                module
                    .coverage_source
                    .iter()
                    .any(|row| row.byte_start == brace.byte_start),
                "braces receive coverage"
            );
        }
        // §12.2, I1: an unknown prose word, with its exact span.
        "LX-06" => {
            let project = mutated(
                "For every natural number",
                "For every banana natural number",
            );
            let error = project.check_fails_with("LLL1004");
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLL1004")
                .expect("just matched");
            let span = diagnostic
                .primary
                .as_ref()
                .expect("an unknown atom has a span");
            let source = project.read("src/Main.lex.tex");
            assert_eq!(
                &source[span.byte_start..span.byte_end],
                "banana",
                "the diagnostic covers exactly the unknown word"
            );
        }
        // §12.2, I2: unknown symbols and controls.
        "LX-07" => {
            mutated("For every", "\\mystery{} For every").check_fails_with("LLL1004");
            mutated("\\(n + 0 = n\\)", "\\(n \u{2297} 0 = n\\)").check_fails_with("LLL1004");
        }
        // §14.1: all form edges, no import-order selection.
        "LX-08" => {
            let ab = ambiguous_project(["test.dupa@1.0.0", "test.dupb@1.0.0"]);
            let ab_error = ab.check_fails_with("LLP2002");
            let ba = ambiguous_project(["test.dupb@1.0.0", "test.dupa@1.0.0"]);
            let ba_error = ba.check_fails_with("LLP2002");
            let message = |error: &lexlean::error::LexLeanError| {
                error
                    .diagnostics
                    .iter()
                    .find(|d| d.code.as_str() == "LLP2002")
                    .expect("matched")
                    .message
                    .clone()
            };
            assert_eq!(
                message(&ab_error),
                message(&ba_error),
                "import order does not change the outcome"
            );
        }
        // I1: every accepted non-whitespace atom is covered exactly once.
        "LX-09" => {
            let project = P::example();
            let checked = support::checked_project(&project);
            let module = &checked.modules["Main"];
            for atom in &module.atoms {
                if atom.class == lexlean::source::atom::AtomClass::Whitespace {
                    continue;
                }
                let covering = module
                    .coverage_source
                    .iter()
                    .filter(|row| {
                        row.byte_start <= atom.byte_start && atom.byte_end <= row.byte_end
                    })
                    .count();
                assert_eq!(
                    covering,
                    1,
                    "atom `{}` at {} is covered exactly once, found {covering}",
                    &module.normalized[atom.byte_start..atom.byte_end],
                    atom.byte_start
                );
            }
        }
        // §14.2: locals exist only through binders and resolve by scope.
        "LX-10" => {
            let unbound = mutated("\\(n + 0 = n\\)", "\\(n + 0 = m\\)");
            let error = unbound.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2002" | "LLL1004" | "LLT4001")),
                "an unbound local fails resolution: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
            // The bound spelling resolves throughout its scope.
            P::example().check_ok();
        }
        // §12.4: TeX definition/expansion/IO controls stay rejected.
        "LX-11" => {
            mutated("For every", "\\def For every").check_fails_with("LLL1004");
            mutated("For every", "\\input{other} For every").check_fails_with("LLL1004");

            let smuggler = P::example();
            smuggler.add_package(
                "lexicons/test-smuggle",
                "test.smuggle",
                &["lexlean.core@1.0.0"],
                &[(
                    "evil.toml",
                    r#"spec = "lexlean/entry/1"
id = "evil"
category = "term-constant"
signature = "(const lexlean.std.nat::nat)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.zero"

[[form]]
id = "evil"
channel = "text"
surface = "\\def"
canonical_source = true
features = []
"#,
                )],
            );
            let error = smuggler
                .engine()
                .lock(lexlean::LockRequest {
                    check_only: false,
                    allow_network: false,
                })
                .err()
                .expect("a package declaring \\def is rejected");
            support::expect_code(&error, "LLR3004");
        }
        // §14.3: explicit qualification selects existing entries only.
        "LX-12" => {
            let qualified = mutated(
                "\\(n + 0 = n\\)",
                "\\(n + \\lexeme{lexlean.std.nat::zero} = n\\)",
            );
            qualified.check_ok();

            let missing = mutated(
                "\\(n + 0 = n\\)",
                "\\(n + \\lexeme{lexlean.std.nat::missing} = n\\)",
            );
            missing.check_fails_with("LLR3005");

            let dangling = mutated(
                "Close the goal by reflexivity.",
                "Close the goal with \\(\\reference{Main::absent}\\).",
            );
            dangling.check_fails_with("LLR3005");
        }
        // §14.4, I5: ambiguity is an error; nothing selects a candidate.
        "LX-13" => {
            let project = ambiguous_project(["test.dupa@1.0.0", "test.dupb@1.0.0"]);
            let error = project.check_fails_with("LLP2002");
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLP2002")
                .expect("matched");
            let rendered = format!("{diagnostic:?}");
            assert!(
                rendered.contains("dupa") && rendered.contains("dupb"),
                "the ambiguity diagnostic names both candidates: {rendered}"
            );
        }
        // §23.5: canonical formatting, with linked-IR preservation.
        "LX-14" => {
            let canonical = P::example();
            canonical.fmt_check_ok();
            let committed = canonical.read("src/Main.lex.tex");
            let expected_semantic = support::checked_project(&canonical).semantic_id;

            let padded = mutated("\n\\begin{theorem}", "\n\n\n\\begin{theorem}");
            assert_eq!(
                support::checked_project(&padded).semantic_id,
                expected_semantic,
                "blank-line variance does not change linked IR"
            );
            padded
                .engine()
                .format(lexlean::FormatRequest {
                    selection: lexlean::Selection::Entrypoints,
                    check_only: false,
                })
                .expect("fmt rewrites");
            assert_eq!(
                padded.read("src/Main.lex.tex"),
                committed,
                "formatting reaches the canonical §29.2 bytes"
            );
            assert_eq!(
                support::checked_project(&padded).semantic_id,
                expected_semantic,
                "formatting preserves linked IR"
            );
        }
        other => panic!("no lexical-closure case is wired for {other}"),
    }
}
