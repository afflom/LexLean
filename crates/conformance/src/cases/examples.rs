//! The `examples` suite: EX-01..EX-08.

use crate::support::{self, P};

pub(crate) fn run(id: &str) {
    match id {
        // §29: the committed example runs the entire pipeline.
        "EX-01" => {
            let example = P::example();
            example.fmt_check_ok();
            let (exit, _, stderr) = example.cli(&["lock", "--check"]);
            assert_eq!(exit, 0, "the committed lock is current: {stderr}");
            example.check_ok();
            if let Some(fixture) = support::example_backed("EX-01") {
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
            // §30.4: the project, lock, and built-in lexicon inputs validate
            // against their committed schemas (TOML read as JSON).
            let example = support::repo_root().join("examples/nat-add-zero");
            support::assert_toml_file_schema("project", &example.join("lexlean.toml"));
            support::assert_toml_file_schema("lock", &example.join("lexlean.lock"));
            for package in ["core", "std/nat"] {
                let package_dir = support::repo_root().join("language").join(package);
                support::assert_toml_file_schema("lexicon", &package_dir.join("lexicon.toml"));
                let mut entries = 0usize;
                for entry in std::fs::read_dir(package_dir.join("entries").as_std_path())
                    .expect("entries")
                    .flatten()
                {
                    let path = camino::Utf8PathBuf::from_path_buf(entry.path()).expect("utf8");
                    if path.extension() == Some("toml") {
                        support::assert_toml_file_schema("entry", &path);
                        entries += 1;
                    }
                }
                assert!(entries > 0, "{package}: entries validated");
            }
        }
        // §29.6 mutation 1: the false proposition fails in Lean, remapped.
        "EX-02" => {
            if !support::lean_backed("EX-02") {
                return;
            }
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
            if !support::lean_backed("EX-05") {
                return;
            }
            let (_, error) = support::axioms_insufficient();
            support::expect_code(error, "LLV7005");
            let rendered = format!("{error}");
            assert!(
                rendered.contains("propext") || rendered.contains("Quot.sound"),
                "the observed excess is recorded: {rendered}"
            );
        }
        // §29.6 mutation 5: two clean `build`s in distinct absolute
        // directories publish byte-identical platform-independent trees.
        "EX-06" => {
            let first = P::example();
            let second = P::example();
            assert_ne!(first.root, second.root, "distinct absolute directories");
            let built_a = first.build_ok();
            let built_b = second.build_ok();
            let id_a = built_a.build_id.expect("build id");
            let id_b = built_b.build_id.expect("build id");
            assert_eq!(
                id_a, id_b,
                "the content-addressed build ID is path independent"
            );
            let dir_a = first.build_dir(&id_a);
            let dir_b = second.build_dir(&id_b);
            let files_a = support::file_set(&dir_a);
            let files_b = support::file_set(&dir_b);
            assert_eq!(files_a, files_b, "the published file sets are equal");
            assert!(
                files_a.contains("manifest.json"),
                "the manifest is published"
            );
            for relative in &files_a {
                let bytes_a = std::fs::read(dir_a.join(relative).as_std_path()).expect("read a");
                let bytes_b = std::fs::read(dir_b.join(relative).as_std_path()).expect("read b");
                assert_eq!(
                    bytes_a, bytes_b,
                    "{relative} differs between the two builds"
                );
                let text = String::from_utf8_lossy(&bytes_a);
                assert!(
                    !text.contains(first.root.as_str()) && !text.contains(second.root.as_str()),
                    "{relative} embeds an absolute checkout path"
                );
            }
        }
        // §28.5, §28.2: every required rejection class has a fixture in the
        // §28.2 layout, each fixture runs through the CLI and equals its
        // committed expectation, and each negative fixture fails with
        // exactly the one prescribed diagnostic code.
        "EX-07" => {
            let root = support::repo_root();
            let prescribed: [(&str, &str); 28] = [
                ("unknown-word", "LLL1004"),
                ("unknown-symbol", "LLL1004"),
                ("unknown-control", "LLL1004"),
                ("raw-percent-comment", "LLL1002"),
                ("raw-lean", "LLF5005"),
                ("raw-lean-declaration", "LLP2003"),
                ("tex-macro", "LLL1002"),
                ("ambiguous-lexical-segmentation", "LLP2002"),
                ("ambiguous-typed-resolution", "LLP2002"),
                ("missing-glossary-entry", "LLR3005"),
                ("lexicon-cycle", "LLR3003"),
                ("unsafe-renderer-control", "LLR3004"),
                ("forward-document-reference", "LLR3005"),
                ("recursive-definition", "LLF5001"),
                ("missing-proof", "LLF5005"),
                ("extra-proof-branch", "LLF5003"),
                ("unrestricted-simplify", "LLF5005"),
                ("native-decide", "LLF5005"),
                ("atlas-level-conflation", "LLT4001"),
                ("lean-elaboration-failure", "LLV7002"),
                ("leanchecker-failure", "LLV7003"),
                ("malformed-axiom-output", "LLV7004"),
                ("axiom-policy-excess", "LLV7005"),
                ("path-symlink", "LLS8001"),
                ("stale-lock", "LLC0102"),
                ("toolchain-mismatch", "LLV7001"),
                ("limit-overrun", "LLS8002"),
                ("pdf-hash-mismatch", "LLS8004"),
            ];
            let negative_root = root.join("tests/negative");
            let mut classes: Vec<String> = std::fs::read_dir(negative_root.as_std_path())
                .expect("tests/negative")
                .flatten()
                .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_dir()))
                .map(|entry| entry.file_name().to_string_lossy().into_owned())
                .collect();
            classes.sort();
            let expected_classes: Vec<&str> = prescribed.iter().map(|(class, _)| *class).collect();
            let mut sorted_expected = expected_classes.clone();
            sorted_expected.sort_unstable();
            assert_eq!(
                classes, sorted_expected,
                "tests/negative holds exactly the prescribed rejection classes (§28.5)"
            );

            let lean_available = support::lean_backed("EX-07");
            let mut failures: Vec<String> = Vec::new();
            for dir in crate::fixtures::discover(&root) {
                let case =
                    crate::fixtures::load_case(&dir).unwrap_or_else(|error| panic!("{error}"));
                let is_lean_backed = case
                    .invocations
                    .iter()
                    .any(|invocation| invocation.command == "verify");
                if is_lean_backed && !lean_available {
                    continue;
                }
                // A checkout without symlink support (Windows with
                // core.symlinks=false) materializes the fixture's symlink as
                // text, so the path-symlink class is host-bound there.
                if cfg!(windows) && dir.ends_with("path-symlink") {
                    eprintln!("EX-07: {dir}: symlink fixture skipped on a host without symlink checkout (§8.3)");
                    continue;
                }
                let observed = match crate::fixtures::check(&dir) {
                    Ok(observed) => observed,
                    Err(error) => {
                        failures.push(error);
                        continue;
                    }
                };
                // §30.4: every emitted diagnostic validates against the
                // diagnostic schema.
                let diagnostics: serde_json::Value =
                    serde_json::from_str(&observed.expected.diagnostics_json)
                        .expect("diagnostics.json parses");
                for (index, diagnostic) in
                    diagnostics.as_array().expect("an array").iter().enumerate()
                {
                    let violations =
                        crate::schema::validate(&support::schema("diagnostic"), diagnostic);
                    if !violations.is_empty() {
                        failures.push(format!(
                            "{dir}: diagnostic {index} violates schemas/diagnostic.schema.json: {}",
                            violations
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join("; ")
                        ));
                    }
                }
                let relative = dir.strip_prefix(&root).unwrap_or(&dir);
                if let Ok(class) = relative.strip_prefix("tests/negative") {
                    let class = class.as_str();
                    let code = prescribed
                        .iter()
                        .find(|(name, _)| *name == class)
                        .map(|(_, code)| *code)
                        .expect("every negative class is prescribed");
                    if observed.codes != [code.to_owned()] {
                        failures.push(format!(
                            "tests/negative/{class}: prescribed exactly [{code}], observed {:?} (§28.5)",
                            observed.codes
                        ));
                    }
                    if observed.exit == 0 {
                        failures.push(format!(
                            "tests/negative/{class}: a negative fixture must fail"
                        ));
                    }
                }
            }
            assert!(
                failures.is_empty(),
                "fixture failures:\n{}",
                failures.join("\n\n")
            );
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
