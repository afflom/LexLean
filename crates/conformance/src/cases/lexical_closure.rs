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

            // Exactly one final LF: surplus final line breaks are
            // noncanonical source that formatting removes.
            let padded = P::example();
            let text = padded.read("src/Main.lex.tex");
            write_bytes(
                &padded,
                "src/Main.lex.tex",
                format!("{text}\n\n").as_bytes(),
            );
            let error = padded.check_fails_with("LLL1003");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| d.code.as_str() == "LLL1003" && !d.help.is_empty()),
                "the surplus-LF diagnostic carries a fix-it"
            );
            let trimmed = lexlean::source::normalize::normalize(
                "src/Main.lex.tex",
                format!("{text}\n\n").as_bytes(),
                true,
            )
            .expect("fmt-mode normalization trims");
            assert_eq!(trimmed.text, text);
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
            mutated("For every", "For\u{3000}every").check_fails_with("LLL1001");
            // Numerals are canonical decimals: a redundant leading zero is
            // noncanonical source with a fix-it and an exact span.
            let zeros = mutated("\\(n + 0 = n\\)", "\\(n + 007 = n\\)");
            let error = zeros.check_fails_with("LLL1003");
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLL1003")
                .expect("matched");
            let span = diagnostic.primary.as_ref().expect("span");
            let text = zeros.read("src/Main.lex.tex");
            assert_eq!(&text[span.byte_start..span.byte_end], "007");
            assert!(diagnostic.help.iter().any(|h| h.contains("`7`")));
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

            // Class 1: letters, or exactly one ASCII nonletter; a backslash
            // before a non-ASCII scalar or at end of file matches no class.
            let controls = lexlean::source::scan::scan("m.lex.tex", "\\(x\\)\\\\\\ \\1\\ab12", 100)
                .expect("scan");
            let control_texts: Vec<(AtomClass, &str)> = controls
                .iter()
                .map(|atom| (atom.class, atom.text.as_str()))
                .collect();
            assert_eq!(
                control_texts,
                vec![
                    (AtomClass::Control, "\\("),
                    (AtomClass::Word, "x"),
                    (AtomClass::Control, "\\)"),
                    (AtomClass::Control, "\\\\"),
                    (AtomClass::Control, "\\ "),
                    (AtomClass::Control, "\\1"),
                    (AtomClass::Control, "\\ab"),
                    (AtomClass::Numeral, "12"),
                ]
            );
            assert_eq!(
                lexlean::source::scan::scan("m.lex.tex", "\\\u{2115}", 100)
                    .expect_err("no atom class")
                    .code
                    .as_str(),
                "LLL1004"
            );
            assert_eq!(
                lexlean::source::scan::scan("m.lex.tex", "a\\", 100)
                    .expect_err("no atom class")
                    .code
                    .as_str(),
                "LLL1004"
            );
            // Class 3 identifiers compose from byte-adjacent atoms only where
            // the grammar requests one; the scanner itself keeps them apart.
            let identifier =
                lexlean::source::scan::scan("m.lex.tex", "x1_2' y", 100).expect("scan");
            assert_eq!(
                lexlean::source::scan::compose_identifier(&identifier, 0),
                Some(("x1_2'".to_owned(), 5))
            );
            assert_eq!(
                lexlean::source::scan::compose_identifier(&identifier, 6),
                Some(("y".to_owned(), 7))
            );
            // DEL and other ASCII controls are no class; normalization
            // rejects them first and the scanner never accepts them.
            assert_eq!(
                lexlean::source::scan::scan("m.lex.tex", "a\u{7F}", 100)
                    .expect_err("DEL")
                    .code
                    .as_str(),
                "LLL1001"
            );
            assert_eq!(
                lexlean::source::normalize::normalize("m.lex.tex", b"a\x7F\n", false)
                    .expect_err("DEL")[0]
                    .code
                    .as_str(),
                "LLL1001"
            );
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

            // The lattice keeps every edge: when the longest form at a word
            // (`even and`) leads to a grammatical dead end, the sentence still
            // parses through the shorter path (`even` + the connective
            // `and`). A greedy longest-match scanner would fail here.
            let overlap = support::defs_project();
            overlap.write(
                "lexicons/test-defs/entries/even.toml",
                &support::adjective_entry("even", "even"),
            );
            overlap.write(
                "lexicons/test-defs/entries/even-and.toml",
                &support::adjective_entry("even-and", "even and"),
            );
            overlap.edit(
                "src/Main.lex.tex",
                "there exists a natural number \\(k\\) such that \\(k = k\\).",
                "for every natural number \\(n\\), \\(n\\) is even and \\(n\\) is even.",
            );
            overlap.relock();
            overlap.check_ok();
            let checked = support::checked_project(&overlap);
            let module = &checked.modules["Main"];
            let forms: Vec<String> = module
                .coverage_source
                .iter()
                .filter_map(|row| match &row.binding {
                    Origin::Form { entry, .. } => Some(entry.clone()),
                    _ => None,
                })
                .collect();
            assert!(
                forms.iter().filter(|entry| *entry == "even").count() == 2
                    && !forms.iter().any(|entry| entry == "even-and"),
                "the non-greedy path is selected: {forms:?}"
            );

            // The lattice is memoized per module and every distinct edge is
            // counted once against `max_token_lattice_edges`, however many
            // grammar passes revisit a position: a connective-rich sentence
            // whose grammar walk revisits its positions repeatedly parses
            // under a budget of its distinct edges (15 here, 18 with slack;
            // counting every revisit needed 23), and a tighter budget fails
            // with `LLS8002` naming the configured value and the observed
            // count.
            let sentence = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{main-goal}\n\\noaxioms\nFor every natural number \\(n\\) and natural number \\(m\\), \\(n + 0 = n\\) and \\(m + 0 = m\\) and \\(n = n\\) or \\(m = m\\) and not \\(n = m\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";
            let budgeted = |limit: u64| -> P {
                let project = P::example();
                project.write("src/Main.lex.tex", sentence);
                project.edit(
                    "lexlean.toml",
                    "max_token_lattice_edges = 4000000",
                    &format!("max_token_lattice_edges = {limit}"),
                );
                project.relock();
                project
            };
            // The statement is what is measured; its proof shape is not
            // under test here, so only the budget diagnostic is asserted.
            if let Err(error) = budgeted(18).engine().check(lexlean::CheckRequest {
                selection: lexlean::Selection::Entrypoints,
            }) {
                assert!(
                    !error
                        .diagnostics
                        .iter()
                        .any(|d| d.code.as_str() == "LLS8002"),
                    "distinct edges fit the budget: {error}"
                );
            }
            let error = budgeted(8).check_fails_with("LLS8002");
            let limit = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLS8002")
                .expect("LLS8002");
            assert!(
                limit.message.contains("max_token_lattice_edges")
                    && limit.message.contains("configured 8")
                    && limit.message.contains("observed"),
                "the limit diagnostic names the limit, its value, and the observation: {}",
                limit.message
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
            // An identifier outside a binder position is not a local: with
            // no glossary form spelling `m`, it is an unknown atom with an
            // exact span.
            let unbound = mutated("\\(n + 0 = n\\)", "\\(n + 0 = m\\)");
            let error = unbound.check_fails_with("LLL1004");
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLL1004")
                .expect("matched");
            let span = diagnostic.primary.as_ref().expect("span");
            let text = unbound.read("src/Main.lex.tex");
            assert_eq!(&text[span.byte_start..span.byte_end], "m");
            // The bound spelling resolves throughout its scope, and an inner
            // binder shadows an outer one.
            P::example().check_ok();
            let shadowed = mutated(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "For every natural number \\(n\\), for every natural number \\(n\\), \\(n + 0 = n\\).",
            );
            shadowed.check_ok();
        }
        // §12.4: TeX definition/expansion/IO controls stay rejected.
        "LX-11" => {
            // §12.4: the forbidden controls are rejected as TeX escapes
            // before any lexical resolution, with an exact span, from the
            // bootstrap list.
            let bootstrap = lexlean::lexicon::load_bootstrap().expect("bootstrap");
            assert_eq!(bootstrap.structural.forbidden_controls.len(), 23);
            for control in &bootstrap.structural.forbidden_controls {
                let project = mutated("For every", &format!("{control} For every"));
                let error = project.check_fails_with("LLL1002");
                let diagnostic = error
                    .diagnostics
                    .iter()
                    .find(|d| d.code.as_str() == "LLL1002")
                    .expect("matched");
                let span = diagnostic.primary.as_ref().expect("span");
                let text = project.read("src/Main.lex.tex");
                assert_eq!(&text[span.byte_start..span.byte_end], control.as_str());
            }
            mutated("For every", "\\input{other} For every").check_fails_with("LLL1002");
            // A control that merely extends a forbidden name is not forbidden
            // (it is unknown instead).
            mutated("For every", "\\define For every").check_fails_with("LLL1004");

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
            // Exactly one diagnostic: the ambiguity, naming exactly the two
            // differentiating qualified candidates in sorted order (the
            // shared `test.dupa::z` is not differentiating) and spanning
            // exactly the ambiguous island `nzz(z)`.
            assert_eq!(error.diagnostics.len(), 1, "one diagnostic: {error:#?}");
            let diagnostic = &error.diagnostics[0];
            assert_eq!(diagnostic.code.as_str(), "LLP2002");
            assert_eq!(
                diagnostic.message,
                "2 distinct linked interpretations survive; the differentiating candidates are: test.dupa::nzz, test.dupb::nzz"
            );
            let source = project.read("src/Main.lex.tex");
            let island_start = source.find("nzz(z)").expect("the module applies nzz");
            let span = diagnostic
                .primary
                .as_ref()
                .expect("the ambiguity carries a span");
            assert_eq!(span.path, "src/Main.lex.tex");
            assert_eq!(
                (span.byte_start, span.byte_end),
                (island_start, island_start + "nzz(z)".len()),
                "the span is exactly the ambiguous island"
            );
            assert_eq!(&source[span.byte_start..span.byte_end], "nzz(z)");
            assert!(diagnostic.labels.is_empty() && diagnostic.notes.is_empty());
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
