//! The `examples` suite: EX-01..EX-08.

use crate::support::{self, P};

/// One parsed negative fixture.
struct NegativeCase {
    class: String,
    kind: String,
    command: String,
    relock: bool,
    codes: Vec<String>,
    edits: Vec<(String, String, String)>,
    test: Option<String>,
    directory: camino::Utf8PathBuf,
}

fn negative_cases() -> Vec<NegativeCase> {
    let root = support::repo_root().join("tests/negative");
    let mut cases = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(root.as_std_path())
        .expect("tests/negative exists")
        .flatten()
        .collect();
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        if !entry.file_type().expect("type").is_dir() {
            continue;
        }
        let directory =
            camino::Utf8PathBuf::from_path_buf(entry.path()).expect("utf8 fixture path");
        let case: toml::Value = toml::from_str(
            &std::fs::read_to_string(directory.join("case.toml").as_std_path()).expect("case.toml"),
        )
        .expect("case.toml parses");
        let string = |key: &str| case.get(key).and_then(|v| v.as_str()).map(str::to_owned);
        cases.push(NegativeCase {
            class: string("class").expect("class"),
            kind: string("kind").expect("kind"),
            command: string("command").unwrap_or_else(|| "check".to_owned()),
            relock: case
                .get("relock")
                .and_then(toml::Value::as_bool)
                .unwrap_or(false),
            codes: case
                .get("codes")
                .and_then(|v| v.as_array())
                .map(|rows| {
                    rows.iter()
                        .filter_map(|row| row.as_str().map(str::to_owned))
                        .collect()
                })
                .unwrap_or_default(),
            edits: case
                .get("edit")
                .and_then(|v| v.as_array())
                .map(|rows| {
                    rows.iter()
                        .map(|row| {
                            (
                                row["file"].as_str().expect("file").to_owned(),
                                row["from"].as_str().expect("from").to_owned(),
                                row["to"].as_str().expect("to").to_owned(),
                            )
                        })
                        .collect()
                })
                .unwrap_or_default(),
            test: string("test"),
            directory,
        });
    }
    cases
}

fn apply_overlay(project: &P, directory: &camino::Utf8Path) {
    let overlay = directory.join("overlay");
    if !overlay.as_std_path().exists() {
        return;
    }
    for entry in walkdir::WalkDir::new(overlay.as_std_path())
        .into_iter()
        .flatten()
    {
        if entry.file_type().is_file() {
            let relative = entry
                .path()
                .strip_prefix(overlay.as_std_path())
                .expect("under overlay")
                .to_string_lossy()
                .replace('\\', "/");
            project.write(
                &relative,
                &std::fs::read_to_string(entry.path()).expect("overlay file"),
            );
        }
    }
}

pub(crate) fn run(id: &str) {
    match id {
        // §29: the committed example runs the entire pipeline.
        "EX-01" => {
            let fixture = support::verified();
            fixture.project.fmt_check_ok();
            let (exit, _, stderr) = fixture.project.cli(&["lock", "--check"]);
            assert_eq!(exit, 0, "the committed lock is current: {stderr}");
            fixture.project.check_ok();
            assert!(
                fixture.attestation["declarations"]
                    .as_array()
                    .expect("declarations")
                    .iter()
                    .any(|row| {
                        row["name"].as_str() == Some("LexLeanExample.Main.add_zero")
                            && row["observed"].as_array().is_some_and(Vec::is_empty)
                    }),
                "§29.5: an empty observed axiom set for the theorem"
            );
        }
        // §29.6 mutation 1: the false proposition fails in Lean, remapped.
        "EX-02" => {
            let (project, error) = support::broken_proof();
            support::expect_code(error, "LLV7002");
            let verified_root = project.root.join(".lexlean/verified");
            if verified_root.as_std_path().exists() {
                assert!(
                    support::file_set(&verified_root).is_empty(),
                    "no verified artifact for a failed proof"
                );
            }
        }
        // §29.6 mutation 2: an undeclared title word fails lexical closure.
        "EX-03" => {
            let project = P::example();
            project.edit(
                "src/Main.lex.tex",
                "\\title{Natural number addition}",
                "\\title{Natural number banana}",
            );
            project.check_fails_with("LLL1004");
        }
        // §29.6 mutation 3: an indistinguishable same-surface proof entry
        // is ambiguity, not priority.
        "EX-04" => {
            let single = P::example();
            single.add_package(
                "lexicons/test-dupa",
                "test.dupa",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[
                    ("nzz.toml", &support::nzz_entry("Nat.le_refl")),
                    ("z.toml", Z_ENTRY),
                ],
            );
            single.write(
                "src/Main.lex.tex",
                &support::nzz_module(&["test.dupa@1.0.0"]),
            );
            single.relock();
            single.check_ok();

            let doubled = P::example();
            doubled.add_package(
                "lexicons/test-dupa",
                "test.dupa",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[
                    ("nzz.toml", &support::nzz_entry("Nat.le_refl")),
                    ("z.toml", Z_ENTRY),
                ],
            );
            doubled.add_package(
                "lexicons/test-dupb",
                "test.dupb",
                &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
                &[("nzz.toml", &support::nzz_entry("Nat.ge_refl"))],
            );
            doubled.write(
                "src/Main.lex.tex",
                &support::nzz_module(&["test.dupa@1.0.0", "test.dupb@1.0.0"]),
            );
            doubled.relock();
            doubled.check_fails_with("LLP2002");
        }
        // §29.6 mutation 4: an insufficient allow-list fails policy, with
        // the observed excess recorded.
        "EX-05" => {
            let (_, error) = support::axioms_insufficient();
            support::expect_code(error, "LLV7005");
            let rendered = format!("{error}");
            assert!(
                rendered.contains("propext") || rendered.contains("Quot.sound"),
                "the observed excess is recorded: {rendered}"
            );
        }
        // §29.6 mutation 5: distinct paths, byte-identical artifacts.
        "EX-06" => {
            let first = support::rendered(&P::example());
            let second = support::rendered(&P::example());
            assert_eq!(first.build_id, second.build_id);
            for ((path_a, bytes_a), (path_b, bytes_b)) in first.files.iter().zip(&second.files) {
                assert_eq!(path_a, path_b);
                assert_eq!(bytes_a, bytes_b, "{path_a}");
            }
        }
        // §28.5: the negative suite covers every required rejection class.
        "EX-07" => {
            let cases = negative_cases();
            let classes: std::collections::BTreeSet<&str> =
                cases.iter().map(|case| case.class.as_str()).collect();
            for required in [
                "unknown-word",
                "unknown-symbol",
                "unknown-control",
                "raw-percent-comment",
                "raw-lean",
                "tex-macro",
                "ambiguous-lexical-segmentation",
                "ambiguous-typed-resolution",
                "missing-glossary-entry",
                "lexicon-cycle",
                "unsafe-renderer-control",
                "forward-document-reference",
                "recursive-definition",
                "missing-proof",
                "extra-proof-branch",
                "unrestricted-simplify",
                "native-decide",
                "lean-elaboration-failure",
                "leanchecker-failure",
                "malformed-axiom-output",
                "axiom-policy-excess",
                "path-symlink",
                "stale-lock",
                "toolchain-mismatch",
                "limit-overrun",
                "pdf-hash-mismatch",
            ] {
                assert!(
                    classes.contains(required),
                    "§28.5: the `{required}` rejection class has a fixture"
                );
            }

            let known_tests = crate::workspace_test_names(support::repo_root().as_std_path());
            for case in &cases {
                match case.kind.as_str() {
                    "mutation" => {
                        let project = P::example();
                        apply_overlay(&project, &case.directory);
                        for (file, from, to) in &case.edits {
                            project.edit(file, from, to);
                        }
                        if case.relock {
                            project.relock();
                        }
                        let error = match case.command.as_str() {
                            "check" => project
                                .engine()
                                .check(lexlean::CheckRequest {
                                    selection: lexlean::Selection::Entrypoints,
                                })
                                .err()
                                .unwrap_or_else(|| {
                                    panic!("{}: check unexpectedly succeeded", case.class)
                                }),
                            "lock" => project
                                .engine()
                                .lock(lexlean::LockRequest {
                                    check_only: false,
                                    allow_network: false,
                                })
                                .err()
                                .unwrap_or_else(|| {
                                    panic!("{}: lock unexpectedly succeeded", case.class)
                                }),
                            "lock-check" => project
                                .engine()
                                .lock(lexlean::LockRequest {
                                    check_only: true,
                                    allow_network: false,
                                })
                                .err()
                                .unwrap_or_else(|| {
                                    panic!("{}: lock --check unexpectedly succeeded", case.class)
                                }),
                            other => panic!("{}: unknown command {other}", case.class),
                        };
                        assert!(
                            error.diagnostics.iter().any(|diagnostic| {
                                case.codes
                                    .iter()
                                    .any(|code| diagnostic.code.as_str() == code)
                            }),
                            "{}: expected one of {:?}, found {:?}",
                            case.class,
                            case.codes,
                            error
                                .diagnostics
                                .iter()
                                .map(|d| d.code.as_str())
                                .collect::<Vec<_>>()
                        );
                    }
                    "delegated" => {
                        let test = case.test.as_ref().unwrap_or_else(|| {
                            panic!("{}: a delegated case names its test", case.class)
                        });
                        assert!(
                            known_tests.contains(test),
                            "{}: delegated to `{test}`, which does not exist",
                            case.class
                        );
                    }
                    other => panic!("{}: unknown kind {other}", case.class),
                }
            }
        }
        // §28.6: every example directory is discovered and gate-complete.
        "EX-08" => {
            let examples = support::repo_root().join("examples");
            let mut found = 0usize;
            for entry in std::fs::read_dir(examples.as_std_path())
                .expect("examples/")
                .flatten()
            {
                if !entry.file_type().expect("type").is_dir() {
                    continue;
                }
                found += 1;
                let directory = camino::Utf8PathBuf::from_path_buf(entry.path()).expect("utf8");
                assert!(
                    directory.join("lexlean.toml").as_std_path().is_file(),
                    "{directory}: every example is a project"
                );
                assert!(
                    directory.join("lexlean.lock").as_std_path().is_file(),
                    "{directory}: every example commits its lock"
                );
                assert!(
                    directory.join("expected/build").as_std_path().is_dir(),
                    "{directory}: every example commits its expected build outputs"
                );
                lexlean::Engine::load(&directory.join("lexlean.toml"))
                    .expect("every discovered example loads");
            }
            assert!(found >= 1, "the example gate has at least one example");
        }
        other => panic!("no examples case is wired for {other}"),
    }
}

const Z_ENTRY: &str = r#"spec = "lexlean/entry/1"
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
