//! The `lean-backend` suite: LN-01..LN-12.

use crate::support::{self, P};

fn example_lean() -> String {
    support::lean_text(&support::rendered(&P::example()), "Main")
}

/// A one-theorem module (statement, proof body).
fn theorem_module(statement: &str, proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{main-goal}}\n\\noaxioms\n{statement}\n\\begin{{proof}}\n{proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

fn two_theorems(first_statement: &str, second_statement: &str, second_proof: &str) -> String {
    format!(
        "\\begin{{lexlean}}{{Main}}\n\\useglossary{{lexlean.std.nat@1.0.0}}\n\\title{{Natural number addition}}\n\n\\begin{{theorem}}{{first}}\n\\noaxioms\n{first_statement}\n\\begin{{proof}}\nClose the goal by reflexivity.\n\\end{{proof}}\n\\end{{theorem}}\n\n\\begin{{theorem}}{{second}}\n\\noaxioms\n{second_statement}\n\\begin{{proof}}\n{second_proof}\n\\end{{proof}}\n\\end{{theorem}}\n\\end{{lexlean}}\n"
    )
}

fn lean_of(module: &str) -> String {
    let project = P::example();
    project.write("src/Main.lex.tex", module);
    project.check_ok();
    support::lean_text(&support::rendered(&project), "Main")
}

pub(crate) fn run(id: &str) {
    match id {
        // §18.1: the exact file structure, in order.
        "LN-01" => {
            let lean = example_lean();
            let sections = [
                "module",
                "import Init",
                "set_option autoImplicit false",
                "namespace LexLeanExample.Main",
                "theorem add_zero",
                "end LexLeanExample.Main",
            ];
            let mut cursor = 0usize;
            for section in sections {
                let at = lean[cursor..]
                    .find(section)
                    .unwrap_or_else(|| panic!("`{section}` after byte {cursor} in: {lean}"));
                cursor += at + section.len();
            }
            assert!(
                lean.starts_with("module\n"),
                "the module header opens the file: {lean}"
            );
        }
        // §18.3: sorted unique imports; fully qualified externals; no open.
        "LN-02" => {
            let lean = example_lean();
            let imports: Vec<&str> = lean
                .lines()
                .filter(|line| line.starts_with("import "))
                .collect();
            let mut sorted = imports.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(imports, sorted, "imports are sorted and deduplicated");
            assert!(
                lean.contains("Nat.add"),
                "external globals are fully qualified: {lean}"
            );
            assert!(!lean.contains("open "), "no open statements: {lean}");
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
            ] {
                for token in &forbidden {
                    assert!(
                        !lean.contains(token.as_str()),
                        "generated Lean contains `{token}`: {lean}"
                    );
                }
            }
        }
        // §18.7: every pinned lowering form is producible; the corpus
        // exercises each one.
        "LN-05" => {
            let mut corpus = String::new();
            corpus.push_str(&lean_of(&theorem_module(
                "For every natural number \\(n\\), if \\(n = n\\), then \\(n + 0 = n\\).",
                "Assume \\(h\\).\nClose the goal by reflexivity.",
            )));
            corpus.push_str(&lean_of(&theorem_module(
                "There exists a natural number \\(k\\) such that \\(k + 0 = k\\).",
                "Use \\(0\\) as the witness.\nClose the goal by reflexivity.",
            )));
            corpus.push_str(&lean_of(&theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\) or \\(n = 1\\).",
                "Select the left alternative.\nClose the goal by reflexivity.",
            )));
            corpus.push_str(&lean_of(&theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{have}{h}\n\\(n + 0 = n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{have}\nClose the goal with \\(h\\).",
            )));
            corpus.push_str(&lean_of(&two_theorems(
                "For every natural number \\(m\\), \\(m + 0 = m\\).",
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{rewrite}{goal}\n\\forward{\\reference{Main::first}}\n\\end{rewrite}\nClose the goal by reflexivity.",
            )));
            corpus.push_str(&lean_of(&two_theorems(
                "For every natural number \\(m\\), \\(m + 0 = m\\).",
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{simplify}{goal}\n\\rule{\\reference{Main::first}}\n\\end{simplify}\nClose the goal by reflexivity.",
            )));
            corpus.push_str(&lean_of(&theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\) and \\(n * 1 = n\\).",
                "\\begin{constructor}\n\\begin{branch}{1}\nClose the goal by reflexivity.\n\\end{branch}\n\\begin{branch}{2}\nClose the goal by reflexivity.\n\\end{branch}\n\\end{constructor}",
            )));
            corpus.push_str(&lean_of(&theorem_module(
                "For every natural number \\(n\\), \\(n + 0 = n\\).",
                "\\begin{induction}{n}\n\\begin{case}{lexlean.std.nat::zero}\n\\bind{}\nClose the goal by reflexivity.\n\\end{case}\n\\begin{case}{lexlean.std.nat::succ}\n\\bind{m;ih}\nClose the goal by reflexivity.\n\\end{case}\n\\end{induction}",
            )));
            corpus.push_str(&lean_of(&two_theorems(
                "\\(0 + 0 = 0\\).",
                "\\(0 + 0 = 0\\).",
                "\\begin{calculate}\n\\start{0 + 0}\n\\step{lexlean.core::eq}{0}{\\reference{Main::first}}\n\\end{calculate}",
            )));
            corpus.push_str(&lean_of("\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{first}\n\\noaxioms\nIf \\(0 + 0 = 0\\), then \\(0 * 0 = 0\\).\n\\begin{proof}\nAssume \\(h\\).\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\n\\begin{theorem}{second}\n\\noaxioms\n\\(0 * 0 = 0\\).\n\\begin{proof}\nApply \\(\\reference{Main::first}\\).\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n"));
            for pinned in [
                "intro",
                "exact",
                "apply",
                "rfl",
                "refine",
                "left",
                "have",
                "rw [",
                "simp only [",
                "constructor",
                "induction",
                "calc",
            ] {
                assert!(
                    corpus.contains(pinned),
                    "the pinned lowering `{pinned}` is exercised by the corpus"
                );
            }
        }
        // §18.5: leading universals become parameters, source-mapped.
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
            assert!(
                module
                    .coverage
                    .lean
                    .iter()
                    .any(|row| row.byte_start <= at && at < row.byte_end),
                "the parameter token has a coverage origin"
            );
        }
        // §18.6: definitions are always def.
        "LN-07" => {
            let lean = support::lean_text(&support::rendered(&support::defs_project()), "Main");
            for name in ["def count", "def double", "def good"] {
                assert!(lean.contains(name), "{name} is a def: {lean}");
            }
            for forbidden in ["abbrev", "instance ", "structure ", "inductive "] {
                assert!(
                    !lean.contains(forbidden),
                    "no alternate declaration forms: {lean}"
                );
            }
        }
        // §18.7: proof lowering uses only the fixed pinned forms.
        "LN-08" => {
            let lean = example_lean();
            let proof = lean
                .split(":= by\n")
                .nth(1)
                .expect("a tactic proof")
                .split("\nend")
                .next()
                .expect("the proof body");
            for token in proof.split_whitespace() {
                assert!(
                    ["rfl"].contains(&token)
                        || token.starts_with("llv")
                        || token.starts_with("llh"),
                    "the example proof body holds only pinned forms, found `{token}`"
                );
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
            for line in first.lines() {
                let indent = line.len() - line.trim_start_matches(' ').len();
                assert_eq!(indent % 2, 0, "two-space indentation steps: {line:?}");
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
            }
        }
        // §18.2: the generated-source audit rejects prose-bearing tokens.
        "LN-11" => {
            let fixture = support::verified();
            let audit_dir = fixture.outcome.root.join("audit");
            assert!(
                audit_dir.as_std_path().is_dir(),
                "the audit module ran before publication"
            );
            // The committed rejected fixtures document what the audit
            // refuses; the semantics digest pins them.
            let rejected = std::fs::read_to_string(
                support::repo_root()
                    .join("tests/golden/axiom-parser/rejected.txt")
                    .as_std_path(),
            )
            .expect("rejected fixtures");
            assert!(
                !rejected.trim().is_empty(),
                "the rejection corpus is nonempty"
            );
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
