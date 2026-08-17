//! The `grammar` suite: GR-01..GR-16.

use crate::support::{self, P};

/// The full generated Lean name prefix of the corpus module.
const M: &str = "LexLeanExample.Main";

/// The example with one replacement in `src/Main.lex.tex`.
fn mutated(from: &str, to: &str) -> P {
    let project = P::example();
    project.edit("src/Main.lex.tex", from, to);
    project
}

/// A one-theorem module with the given statement and proof body.
fn theorem_module(statement: &str, proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{shape}}\n\\noaxioms\n{statement}\n\\begin{{proof}}\n{proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

/// The generated Lean statement line of one corpus declaration.
///
/// The header is a `build` product asserted on every supported host; the
/// corpus attestation behind it needs the pinned toolchain (§8.3).
fn corpus_header(id: &str, lean_name: &str) -> String {
    if let Some(fixture) = support::corpus_backed(id) {
        assert_eq!(fixture.attestation["status"], "verified");
    }
    support::corpus_declaration_lean(lean_name)
        .lines()
        .next()
        .expect("a header line")
        .to_owned()
}

/// Check a module, expecting the given failure code, and return the
/// matching diagnostic.
fn fails_with(module: &str, code: &str) -> lexlean::diagnostic::Diagnostic {
    let project = P::example();
    project.write("src/Main.lex.tex", module);
    let error = project.check_err();
    support::expect_code(&error, code);
    error
        .diagnostics
        .into_iter()
        .find(|d| d.code.as_str() == code)
        .expect("matched")
}

/// The generated Lean of a checked one-theorem module.
fn lean_of(module: &str) -> String {
    let project = P::example();
    project.write("src/Main.lex.tex", module);
    project.check_ok();
    support::lean_text(&support::rendered(&project), "Main")
}

/// A zero-arity entry whose one form covers `surface` on `channel`: the
/// building block of a token lattice whose local segmentation is ambiguous.
fn segment_entry(id: &str, surface: &str, channel: &str, category: &str) -> String {
    // A label-word carries no signature and no math rendering (§13.3); a
    // term constant carries both.
    let word = category == "label-word";
    let signature = if word {
        String::new()
    } else {
        "signature = \"(const lexlean.std.nat::nat)\"\n".to_owned()
    };
    let features = if word {
        "\"sentence-case\", \"singular\""
    } else {
        ""
    };
    let render = if word {
        String::new()
    } else {
        format!("\n[render]\nmath = \"(operator-name {id})\"\n")
    };
    format!(
        "spec = \"lexlean/entry/1\"\nid = \"{id}\"\ncategory = \"{category}\"\n{signature}surface_arity = 0\nframe = \"atom\"\n\n[denotation]\nkind = \"lean\"\nmodule = \"Init\"\nname = \"Nat.zero\"\n\n[[form]]\nid = \"{id}\"\nchannel = \"{channel}\"\nsurface = \"{surface}\"\ncanonical_source = true\nfeatures = [{features}]\n{render}"
    )
}

/// A project whose glossary carries exactly the named segmenting entries,
/// with the given module source.
fn segmenting_project(entries: &[(&str, &str, &str, &str)], module: &str) -> P {
    let bodies: Vec<(String, String)> = entries
        .iter()
        .map(|(id, surface, channel, category)| {
            (
                format!("{id}.toml"),
                segment_entry(id, surface, channel, category),
            )
        })
        .collect();
    let refs: Vec<(&str, &str)> = bodies
        .iter()
        .map(|(name, body)| (name.as_str(), body.as_str()))
        .collect();
    let project = P::example();
    project.add_package(
        "lexicons/test-seg",
        "test.seg",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        &refs,
    );
    project.write("src/Main.lex.tex", module);
    project.relock();
    project
}

pub(crate) fn run(id: &str) {
    match id {
        // §15.1: only the fixed environment set parses.
        "GR-01" => {
            mutated(
                "\\begin{theorem}{add-zero}",
                "\\begin{conjecture}{add-zero}",
            )
            .check_fails_with("LLL1004");
            mutated("\\begin{theorem}", "stray words\n\\begin{theorem}")
                .check_fails_with("LLP2003");
        }
        // §15.1, GR-02: exact header order and cardinality.
        "GR-02" => {
            let late_glossary = mutated(
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}",
                "\\title{Natural number addition}\n\\useglossary{lexlean.std.nat@1.0.0}",
            );
            late_glossary.check_fails_with("LLP2003");

            mutated(
                "\\title{Natural number addition}",
                "\\title{Natural number addition}\n\\title{Natural number addition}",
            )
            .check_fails_with("LLP2003");

            mutated("\\title{Natural number addition}\n", "").check_fails_with("LLP2003");
        }
        // §15.1, §25.5: every nesting is bounded by the configured scope
        // limit and reported, never a stack overflow; parameters introduce
        // explicit inherited context.
        "GR-03" => {
            let sectioned = P::example();
            sectioned.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{section}{basics}\n\\heading{Natural number addition}\n\\parameters{natural number \\(n\\)}\n\\begin{theorem}{param-use}\n\\noaxioms\n\\(n + 0 = n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{section}\n\\end{lexlean}\n",
            );
            sectioned.check_ok();

            // The same configured limit bounds glossary LSE/LRE nesting
            // (the embedded core needs a small depth), so the source test
            // nests sections one level beyond a limit the glossary meets.
            let deep = P::example();
            deep.edit(
                "lexlean.toml",
                "max_scope_depth = 1024",
                "max_scope_depth = 12",
            );
            deep.relock();
            let mut nested = String::from(
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n",
            );
            for level in 0..13u32 {
                nested.push_str(&format!(
                    "\n\\begin{{section}}{{level-{level}}}\n\\heading{{Natural number addition}}\n"
                ));
            }
            for _ in 0..13u32 {
                nested.push_str("\\end{section}\n");
            }
            nested.push_str("\\end{lexlean}\n");
            deep.write("src/Main.lex.tex", &nested);
            deep.check_fails_with("LLS8002");
            // One level fewer stays within the limit.
            let within = P::example();
            within.edit(
                "lexlean.toml",
                "max_scope_depth = 1024",
                "max_scope_depth = 12",
            );
            within.relock();
            let mut nested = String::from(
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n",
            );
            for level in 0..12u32 {
                nested.push_str(&format!(
                    "\n\\begin{{section}}{{level-{level}}}\n\\heading{{Natural number addition}}\n"
                ));
            }
            for _ in 0..12u32 {
                nested.push_str("\\end{section}\n");
            }
            nested.push_str("\\end{lexlean}\n");
            within.write("src/Main.lex.tex", &nested);
            within.check_ok();

            // 100000 nested grouping parentheses: LLS8002 naming the limit,
            // its value, and the phase --- not an abort (C1).
            let parens = format!("{}n{}", "(".repeat(100_000), ")".repeat(100_000));
            let diagnostic = fails_with(
                &theorem_module(
                    &format!("For every natural number \\(n\\), \\({parens} + 0 = n\\)."),
                    "Close the goal by reflexivity.",
                ),
                "LLS8002",
            );
            assert!(
                diagnostic.message.contains("max_scope_depth")
                    && diagnostic.message.contains("1024")
                    && diagnostic.message.contains("parse"),
                "the depth diagnostic names the limit, value, and phase: {}",
                diagnostic.message
            );
            assert!(
                diagnostic.primary.is_some(),
                "the depth diagnostic has a span"
            );
            // 20000 nested `have` environments likewise.
            let mut proof = String::new();
            for _ in 0..20_000 {
                proof.push_str("\\begin{have}{h}\n\\(n + 0 = n\\).\n\\begin{proof}\n");
            }
            proof.push_str("Close the goal by reflexivity.\n");
            for _ in 0..20_000 {
                proof.push_str("\\end{proof}\n\\end{have}\nClose the goal with \\(h\\).\n");
            }
            let diagnostic = fails_with(
                &theorem_module("For every natural number \\(n\\), \\(n + 0 = n\\).", &proof),
                "LLS8002",
            );
            assert!(
                diagnostic.message.contains("proof environment nesting"),
                "{}",
                diagnostic.message
            );
            // 5000 nested negations in a proposition likewise.
            let nots = format!("{}\\(n = n\\)", "not ".repeat(5_000));
            let diagnostic = fails_with(
                &theorem_module(
                    &format!("For every natural number \\(n\\), {nots}."),
                    "Close the goal by reflexivity.",
                ),
                "LLS8002",
            );
            assert!(
                diagnostic.message.contains("proposition nesting"),
                "{}",
                diagnostic.message
            );
        }
        // §15.3: titles and headings cannot encode a proposition; a noun-of
        // term phrase is a phrase item.
        "GR-04" => {
            let error =
                mutated("\\title{Natural number addition}", "\\title{\\(ℕ = ℕ\\)}").check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2001" | "LLP2003" | "LLT4001")),
                "a title cannot encode a proposition: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
            // A predicate frame in a heading is rejected; a noun-of term
            // phrase over a numeral is accepted and formats canonically.
            let project = support::corpus_project();
            project.edit(
                "src/Main.lex.tex",
                "\\heading{Natural number addition}",
                "\\heading{Natural number addition: the double of \\(0\\)}",
            );
            let checked = support::checked_project(&project);
            let canonical =
                lexlean::fmt::canonical_source(&checked.modules["Main"], &checked.closure)
                    .expect("formats");
            assert!(
                canonical.contains("\\heading{Natural number addition: the double of \\(0\\)}"),
                "the noun-of phrase item round-trips: {canonical}"
            );
            project.edit(
                "src/Main.lex.tex",
                "\\heading{Natural number addition: the double of \\(0\\)}",
                "\\heading{\\(0\\) is even}",
            );
            let error = project.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLL1004" | "LLP2001" | "LLP2003")),
                "a predicate frame is not a phrase: {error}"
            );
        }
        // §15.5: only \( \) and \[ \] make islands; dollars are rejected;
        // nested calls and grouped arguments cover exactly their own
        // delimiters (S1).
        "GR-05" => {
            mutated("\\(n + 0 = n\\)", "$n + 0 = n$").check_fails_with("LLP2001");
            mutated("\\(n + 0 = n\\)", "\\[n + 0 = n\\]").check_ok();
            let lean = lean_of(&theorem_module(
                "For every natural number \\(n\\), \\(succ(succ((n + 0))) = succ(succ(n))\\).",
                "Close the goal by reflexivity.",
            ));
            assert!(
                lean.contains(
                    "Eq (Nat.succ (Nat.succ (Nat.add llv0 0))) (Nat.succ (Nat.succ llv0))"
                ),
                "nested calls with a grouped argument elaborate: {lean}"
            );
            assert_eq!(
                corpus_header("GR-05", "nested_call"),
                format!("public theorem nested_call (llv0 : Nat) (llv1 : Nat) : Eq (Nat.add (Nat.succ llv0) ({M}.combine (Nat.add llv1 0) llv0)) (Nat.add ({M}.combine (Nat.add llv1 0) llv0) (Nat.succ llv0)) := by"),
                "a two-argument call with nested and grouped arguments"
            );
        }
        // §15.5: declared precedence and associativity govern operators; the
        // whole scale `0..255` is usable (C8).
        "GR-06" => {
            let precedence = mutated("\\(n + 0 = n\\)", "\\(n + n * n = n\\)");
            precedence.check_ok();
            let lean = support::lean_text(&support::rendered(&precedence), "Main");
            assert!(
                lean.contains("Nat.add llv0 (Nat.mul llv0 llv0)"),
                "* binds tighter than +, found: {lean}"
            );

            let associativity = mutated("\\(n + 0 = n\\)", "\\(n + n + n = n\\)");
            associativity.check_ok();
            let lean = support::lean_text(&support::rendered(&associativity), "Main");
            assert!(
                lean.contains("Nat.add (Nat.add llv0 llv0) llv0"),
                "+ associates left, found: {lean}"
            );

            // `=` is nonassociative: an unparenthesized chain is an error.
            mutated("\\(n + 0 = n\\)", "\\(n = n = n\\)").check_fails_with("LLP2004");

            // Precedence 255 (the top of the scale) parses and formats.
            let top = P::example();
            top.add_package(
                "lexicons/test-prec",
                "test.prec",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("bump.toml", BUMP_ENTRY)],
            );
            top.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.prec@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{top}\n\\noaxioms\nFor every natural number \\(n\\), \\(n ⊕ n ⊕ 0 = n + n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n",
            );
            top.relock();
            top.check_ok();
            let lean = support::lean_text(&support::rendered(&top), "Main");
            assert!(
                lean.contains("Eq (Nat.add (Nat.add llv0 llv0) 0) (Nat.add llv0 llv0)"),
                "a precedence-255 left-associative operator chains: {lean}"
            );
            let checked = support::checked_project(&top);
            let canonical =
                lexlean::fmt::canonical_source(&checked.modules["Main"], &checked.closure)
                    .expect("formats");
            assert!(
                canonical.contains("\\(n ⊕ n ⊕ 0 = n + n\\)"),
                "precedence 255 formats without overflow: {canonical}"
            );
        }
        // §15.5: juxtaposition is never multiplication or application.
        "GR-07" => {
            let error = mutated("\\(n + 0 = n\\)", "\\(n n = n\\)").check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2004" | "LLP2001")),
                "juxtaposition has no reading: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §15.6: the compositional semantics of every proposition form,
        // Lean-verified in the corpus and exact in the generated statement.
        "GR-08" => {
            assert_eq!(
                corpus_header("GR-08", "constructor_and"),
                "public theorem constructor_and (llv0 : Nat) : And (Eq (Nat.add llv0 0) llv0) (Eq (Nat.add 0 llv0) llv0) := by"
            );
            assert_eq!(
                corpus_header("GR-08", "cases_nat"),
                "public theorem cases_nat (llv0 : Nat) : Or (Eq (Nat.add llv0 0) llv0) (Eq llv0 (1 : Nat)) := by"
            );
            assert_eq!(
                corpus_header("GR-08", "not_both"),
                "public theorem not_both (llv0 : Nat) : Not (And (Eq llv0 llv0) (Not (Eq llv0 llv0))) := by"
            );
            assert_eq!(
                corpus_header("GR-08", "exists_witness"),
                "public theorem exists_witness : Exists (fun (llv0 : Nat) => Eq (Nat.add llv0 0) (0 : Nat)) := by"
            );
            assert_eq!(
                corpus_header("GR-08", "exists_unique"),
                "public theorem exists_unique : Exists (fun (llv0 : Nat) => And (Eq llv0 (0 : Nat)) ((llv1 : Nat) → (Eq llv1 (0 : Nat)) → Eq llv1 llv0)) := by",
                "unique existence lowers to its Exists definition"
            );
            assert_eq!(
                corpus_header("GR-08", "or_comm"),
                "public theorem or_comm (llv0 : Nat) : (Or (Eq llv0 (0 : Nat)) (Eq llv0 (1 : Nat))) → Or (Eq llv0 (1 : Nat)) (Eq llv0 (0 : Nat)) := by",
                "`if P, then Q` is an arrow"
            );
            assert_eq!(
                corpus_header("GR-08", "implies_rewrite"),
                "public theorem implies_rewrite (llv0 : Nat) : (Eq llv0 (1 : Nat)) → Eq (Nat.add llv0 0) (1 : Nat) := by",
                "`P implies Q` is an arrow"
            );
            assert_eq!(
                corpus_header("GR-08", "constructor_iff"),
                "public theorem constructor_iff (llv0 : Nat) : Iff (Eq (Nat.add llv0 0) llv0) (Eq llv0 llv0) := by"
            );
            assert_eq!(
                corpus_header("GR-08", "add_succ"),
                "public theorem add_succ (llv0 : Nat) (llv1 : Nat) : Eq (Nat.add llv0 (Nat.succ llv1)) (Nat.succ (Nat.add llv0 llv1)) := by",
                "a multi-binder universal lifts every binder to a parameter"
            );
        }
        // §15.6: fixed precedence yields one parse; `and` binds under `or`.
        "GR-09" => {
            let lean = lean_of(&theorem_module(
                "For every natural number \\(n\\), if \\(n = n\\) and \\(n = 0\\) or \\(n = 0\\), then \\(n + 0 = n\\).",
                "Assume \\(h\\).\nClose the goal by reflexivity.",
            ));
            assert!(
                lean.contains(
                    "(Or (And (Eq llv0 llv0) (Eq llv0 (0 : Nat))) (Eq llv0 (0 : Nat))) → Eq (Nat.add llv0 0) llv0"
                ),
                "`P and Q or R` parses as Or(And(P,Q),R): {lean}"
            );
        }
        // §13.5, §15.6: articles, plurals, and capitalization are lexicon
        // data; `there exists` requires its article; sentence-case keyword
        // spellings are accepted only at the sentence start (C14).
        "GR-10" => {
            let error =
                mutated("For every natural number", "For every natural numbers").check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2001" | "LLL1004")),
                "a plural form in a singular slot has no inferred reading: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
            let nat_entry = std::fs::read_to_string(
                support::repo_root()
                    .join("language/std/nat/entries/nat.toml")
                    .as_std_path(),
            )
            .expect("nat entry");
            for datum in ["article-a", "plural", "sentence-case", "singular"] {
                assert!(
                    nat_entry.contains(datum),
                    "inflection `{datum}` is explicit lexicon data"
                );
            }
            fails_with(
                &theorem_module(
                    "There exists natural number \\(k\\) such that \\(k = 0\\).",
                    "Use \\(0\\) as the witness.\nClose the goal by reflexivity.",
                ),
                "LLP2001",
            );
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), If \\(n = n\\), then \\(n + 0 = n\\).",
                    "Assume \\(h\\).\nClose the goal by reflexivity.",
                ),
                "LLP2001",
            );
            fails_with(
                &theorem_module(
                    "For every natural number \\(n\\), \\(n = n\\) and Not \\(n = 1\\).",
                    "Close the goal by reflexivity.",
                ),
                "LLP2001",
            );
        }
        // §15.6: a failed parse is a bounded structured diagnostic.
        "GR-11" => {
            let error = mutated(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "For every natural number \\(n\\), such that.",
            )
            .check_err();
            let diagnostic = error.diagnostics.first().expect("a structured diagnostic");
            assert_eq!(diagnostic.code.as_str(), "LLP2001");
            assert!(diagnostic.primary.is_some(), "the diagnostic has a span");
            assert!(
                diagnostic.message.len() < 1_000,
                "the diagnostic is bounded, not a dump"
            );
            assert!(
                error.diagnostics.len() <= 256,
                "diagnostics respect max_diagnostics"
            );
            // An unknown composed identifier (§12.2 class 3) is named whole,
            // not by its first atom.
            let error = mutated("\\(n + 0 = n\\)", "\\(x_1 + 0 = n\\)").check_err();
            let unknown = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLL1004")
                .unwrap_or_else(|| panic!("an unknown identifier is LLL1004: {error}"));
            assert!(
                unknown.message.contains("`x_1`"),
                "the composed identifier is named whole: {}",
                unknown.message
            );
        }
        // §14.4: distinct parses are ambiguity naming the differentiating
        // candidates; identical IR collapses.
        "GR-12" => {
            // §14.1, §14.4: a phrase whose covers are exponentially many
            // (overlapping one- and two-word forms) decides on the first
            // two distinct linked interpretations, so the decision costs
            // covers, not the whole cover space.
            let overlapping = P::example();
            overlapping.add_package(
                "lexicons/test-overlap",
                "test.overlap",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[
                    ("one.toml", &support::label_word_entry("one", "wa")),
                    ("two.toml", &support::label_word_entry("two", "wa wa")),
                ],
            );
            overlapping.edit(
                "src/Main.lex.tex",
                "\\useglossary{lexlean.std.nat@1.0.0}",
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.overlap@1.0.0}",
            );
            let title: String = std::iter::repeat_n("wa", 24).collect::<Vec<_>>().join(" ");
            overlapping.edit(
                "src/Main.lex.tex",
                "\\title{Natural number addition}",
                &format!("\\title{{{title}}}"),
            );
            overlapping.relock();
            let start = std::time::Instant::now();
            overlapping.check_fails_with("LLP2002");
            assert!(
                start.elapsed() < std::time::Duration::from_secs(10),
                "the ambiguity decision reads covers, not the cover space: {:?}",
                start.elapsed()
            );

            let distinct = P::example();
            distinct.add_package(
                "lexicons/test-dupa",
                "test.dupa",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[
                    ("nzz.toml", &support::nzz_entry("Nat.le_refl")),
                    ("z.toml", Z_LOCAL),
                ],
            );
            distinct.add_package(
                "lexicons/test-dupb",
                "test.dupb",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("nzz.toml", &support::nzz_entry("Nat.ge_refl"))],
            );
            distinct.write(
                "src/Main.lex.tex",
                &support::nzz_module(&["test.dupa@1.0.0", "test.dupb@1.0.0"]),
            );
            distinct.relock();
            let error = distinct.check_fails_with("LLP2002");
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|d| d.code.as_str() == "LLP2002")
                .expect("matched");
            assert!(
                diagnostic.message.contains("test.dupa::nzz")
                    && diagnostic.message.contains("test.dupb::nzz")
                    && !diagnostic.message.contains("test.dupa::z"),
                "only the differentiating candidates are listed: {}",
                diagnostic.message
            );
            assert!(diagnostic.primary.is_some(), "the ambiguity has a span");

            // Two forms of one entry share a surface: both candidates
            // elaborate to the same linked IR and collapse (§14.4).
            let collapsing = P::example();
            let doubled_form = support::nzz_entry("Nat.le_refl").replace(
                "[render]",
                "[[form]]\nid = \"nzz-alt\"\nchannel = \"math\"\nsurface = \"nzz\"\ncanonical_source = false\nfeatures = []\n\n[render]",
            );
            collapsing.add_package(
                "lexicons/test-dupa",
                "test.dupa",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("nzz.toml", &doubled_form), ("z.toml", Z_LOCAL)],
            );
            collapsing.write(
                "src/Main.lex.tex",
                &support::nzz_module(&["test.dupa@1.0.0"]),
            );
            collapsing.relock();
            collapsing.check_ok();

            // §14.1: segmentation is a lattice, not a greedy choice. `Wa Wb`
            // is covered by the long label-word and, at the same position,
            // started by the short one; only the long form completes a cover
            // because nothing covers `Wb`, so exactly one linked phrase
            // survives and the module checks. Committing to the first extent
            // at that position would reject a program with one parse.
            let phrase_module = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.seg@1.0.0}\n\\title{Wa Wb}\n\n\\begin{theorem}{add-zero}\n\\noaxioms\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";
            segmenting_project(
                &[
                    ("wab", "Wa Wb", "text", "label-word"),
                    ("wa", "Wa", "text", "label-word"),
                ],
                phrase_module,
            )
            .check_ok();
            // The short extent really is a dead end: with only it in the
            // glossary the phrase has no cover at all.
            let dead_end = segmenting_project(&[("wa", "Wa", "text", "label-word")], phrase_module);
            let error = dead_end.check_fails_with("LLL1004");
            assert!(
                error.diagnostics.iter().any(|d| d.message.contains("`Wb`")),
                "the uncovered token is named: {error}"
            );

            // The same in a mathematical island, where the leaf loop made
            // the same greedy commitment.
            let island_module = "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\useglossary{test.seg@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{pq-refl}\n\\noaxioms\n\\(p q = p q\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n";
            segmenting_project(
                &[
                    ("pq", "p q", "math", "term-constant"),
                    ("pp", "p", "math", "term-constant"),
                ],
                island_module,
            )
            .check_ok();
            segmenting_project(&[("pp", "p", "math", "term-constant")], island_module).check_err();
        }
        // §15.6: free expository text and opaque nodes are rejected.
        "GR-13" => {
            let error = mutated("\\begin{proof}", "This is obvious.\n\\begin{proof}").check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLP2003" | "LLF5005")),
                "expository prose inside a component is rejected: {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
            mutated("\\begin{theorem}", "This is obvious.\n\\begin{theorem}")
                .check_fails_with("LLP2003");
            mutated("\\(n + 0 = n\\)", "\\text{obvious}").check_fails_with("LLL1004");
        }
        // §15.8: exact sentence, policy, and proof cardinalities.
        "GR-14" => {
            mutated(
                "\\end{proof}\n\\end{theorem}",
                "\\end{proof}\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}",
            )
            .check_fails_with("LLP2003");
            mutated("\\noaxioms\n", "").check_fails_with("LLP2003");
        }
        // §15.1: module imports are acyclic; closure is included.
        "GR-15" => {
            let project = P::example();
            project.write(
                "src/Helper.lex.tex",
                "\\begin{lexlean}{Helper}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{helper-fact}\n\\noaxioms\nFor every natural number \\(m\\), \\(m + 0 = m\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n",
            );
            project.edit(
                "src/Main.lex.tex",
                "\\useglossary{lexlean.std.nat@1.0.0}",
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\importmodule{Helper}",
            );
            let checked = project.check_ok();
            assert_eq!(
                checked.units.keys().cloned().collect::<Vec<_>>(),
                vec!["Helper".to_owned(), "Main".to_owned()],
                "the transitive import closure is part of the result set"
            );

            project.edit(
                "src/Helper.lex.tex",
                "\\useglossary{lexlean.std.nat@1.0.0}",
                "\\useglossary{lexlean.std.nat@1.0.0}\n\\importmodule{Main}",
            );
            project.check_fails_with("LLR3003");
        }
        // §15.1: no same-module reference to a later declaration.
        "GR-16" => {
            let forward = P::example();
            forward.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{first-fact}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal with \\(\\reference{Main::second-fact}\\).\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{second-fact}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n",
            );
            forward.check_fails_with("LLR3005");

            let backward = P::example();
            backward.write(
                "src/Main.lex.tex",
                "\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{first-fact}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{second-fact}\n\\noaxioms\n\\(0 + 0 = 0\\).\n\\begin{proof}\nClose the goal with \\(\\reference{Main::first-fact}\\).\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n",
            );
            backward.check_ok();
        }
        other => panic!("no grammar case is wired for {other}"),
    }
}

/// The math-channel zero used by the duplicate fixtures.
const Z_LOCAL: &str = r#"spec = "lexlean/entry/1"
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

/// A precedence-255 left-associative infix operator denoting `Nat.add`.
const BUMP_ENTRY: &str = r#"spec = "lexlean/entry/1"
id = "bump"
category = "infix-function"
signature = "(pi ((explicit a (const lexlean.std.nat::nat)) (explicit b (const lexlean.std.nat::nat))) (const lexlean.std.nat::nat))"
surface_arity = 2
frame = "infix"
precedence = 255
associativity = "left"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.add"

[[form]]
id = "bump"
channel = "math"
surface = "⊕"
canonical_source = true
features = []

[render]
math = "(seq (slot 0) (space) (token plus) (space) (slot 1))"
"#;
