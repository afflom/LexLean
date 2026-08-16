//! The `cli-api` suite: CL-01..CL-18.

use std::panic::{catch_unwind, AssertUnwindSafe};

use lexlean::{CheckRequest, Engine, ErrorClass, Selection};

use crate::support::{self, P};

fn api_source() -> String {
    std::fs::read_to_string(
        support::repo_root()
            .join("crates/lexlean/src/api.rs")
            .as_std_path(),
    )
    .expect("api.rs")
}

pub(crate) fn run(id: &str) {
    match id {
        // §23.1, §23.2: the exact global-option contract.
        "CL-01" => {
            let project = P::example();
            let elsewhere = tempfile::tempdir().expect("tempdir");
            let config = project.root.join("lexlean.toml");
            let outside = camino::Utf8Path::from_path(elsewhere.path()).expect("utf8");
            let (exit, _, stderr) =
                support::cli_in(outside, &["--project", config.as_str(), "check"]);
            assert_eq!(exit, 0, "--project selects the project: {stderr}");
            let (exit, _, _) = support::cli_in(outside, &["check"]);
            assert_eq!(exit, 2, "no discoverable project is CLI misuse");
            let (exit, _, _) = project.cli(&["--frobnicate", "check"]);
            assert_eq!(exit, 2, "unknown global options are misuse");
            let (exit, stdout, _) = project.cli(&["--help"]);
            assert_eq!(exit, 0);
            assert!(stdout.contains("--project") && stdout.contains("--diagnostic-format"));
        }
        // §23.4: init creates the complete skeleton, never overwriting.
        "CL-02" => {
            let target = tempfile::tempdir().expect("tempdir");
            let target_path = camino::Utf8Path::from_path(target.path()).expect("utf8");
            let (exit, _, stderr) = support::cli_in(
                target_path,
                &["init", ".", "--name", "fresh", "--module-prefix", "Fresh"],
            );
            assert_eq!(exit, 0, "init succeeds in an empty directory: {stderr}");
            let files = support::file_set(target_path);
            for required in [
                "lexlean.toml",
                "lexlean.lock",
                "lean-toolchain",
                "src/Main.lex.tex",
                ".gitignore",
            ] {
                assert!(
                    files.contains(required),
                    "init writes {required}: {files:?}"
                );
            }
            let engine = Engine::load(&target_path.join("lexlean.toml")).expect("loads");
            engine
                .check(CheckRequest {
                    selection: Selection::Entrypoints,
                })
                .expect("the canonical skeleton checks");

            let (exit, _, _) = support::cli_in(
                target_path,
                &["init", ".", "--name", "again", "--module-prefix", "Again"],
            );
            assert_eq!(exit, 2, "init never overwrites a nonempty destination");
        }
        // §23.4: the three lock modes are exact and exclusive.
        "CL-03" => {
            let project = P::example();
            let (exit, _, _) = project.cli(&["lock", "--check", "--allow-network"]);
            assert_eq!(exit, 2, "--check and --allow-network are exclusive");
            let (exit, _, _) = project.cli(&["lock", "--check"]);
            assert_eq!(exit, 0, "a current lock passes --check");
            project.edit(
                "lexlean.toml",
                "max_diagnostics = 256",
                "max_diagnostics = 128",
            );
            let (exit, _, _) = project.cli(&["lock", "--check"]);
            assert_ne!(exit, 0, "drift fails --check");
            let (exit, _, _) = project.cli(&["lock"]);
            assert_eq!(exit, 0, "a local update rewrites");
            let (exit, _, _) = project.cli(&["lock", "--check"]);
            assert_eq!(exit, 0, "and the rewritten lock is current");
        }
        // §23.4: check emits no build artifacts.
        "CL-04" => {
            let project = P::example();
            let (exit, _, _) = project.cli(&["check"]);
            assert_eq!(exit, 0);
            assert!(
                !project.root.join(".lexlean/build").as_std_path().exists(),
                "check writes nothing under the build root"
            );
        }
        // §23.4: build never runs Lean and never claims verification.
        "CL-05" => {
            let empty_elan = tempfile::tempdir().expect("tempdir");
            let fake = empty_elan.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&fake))], || {
                let project = P::example();
                let build = project.build_ok();
                assert!(
                    build.build_id.is_some(),
                    "build succeeds without any toolchain"
                );
            });
        }
        // §23.4: verify accepts no output or suppression options.
        "CL-06" => {
            let project = P::example();
            for arguments in [
                ["verify", "--output", "elsewhere"].as_slice(),
                ["verify", "--skip-probe"].as_slice(),
                ["verify", "--fast"].as_slice(),
            ] {
                let (exit, _, _) = project.cli(arguments);
                assert_eq!(exit, 2, "verify rejects {arguments:?}");
            }
        }
        // §23.5: formatting is idempotent and IR-preserving.
        "CL-07" => {
            let project = P::example();
            let before = project.read("src/Main.lex.tex");
            let semantic = support::checked_project(&project).semantic_id;
            let (exit, _, _) = project.cli(&["fmt"]);
            assert_eq!(exit, 0);
            assert_eq!(
                project.read("src/Main.lex.tex"),
                before,
                "already canonical"
            );
            let (exit, _, _) = project.cli(&["fmt", "--check"]);
            assert_eq!(exit, 0, "fmt --check agrees");
            assert_eq!(
                support::checked_project(&project).semantic_id,
                semantic,
                "formatting preserves linked IR"
            );
        }
        // §23.4: clean removes exactly the validated build root.
        "CL-08" => {
            let project = P::example();
            project.build_ok();
            project.write("src/keep.txt", "survives\n");
            let (exit, _, _) = project.cli(&["clean"]);
            assert_eq!(exit, 0);
            assert!(!project.root.join(".lexlean").as_std_path().exists());
            assert!(project.root.join("src/keep.txt").as_std_path().exists());

            // A symlinked build root is refused and its target survives.
            let victim = tempfile::tempdir().expect("tempdir");
            std::fs::write(victim.path().join("precious.txt"), b"data").expect("write");
            std::os::unix::fs::symlink(victim.path(), project.root.join(".lexlean").as_std_path())
                .expect("symlink");
            let (exit, _, _) = project.cli(&["clean"]);
            assert_ne!(exit, 0, "a symlinked build root is refused");
            assert!(
                victim.path().join("precious.txt").exists(),
                "the symlink target is untouched"
            );
        }
        // §23.4: explain prints exactly one registered entry.
        "CL-09" => {
            let project = P::example();
            let (exit, stdout, _) = project.cli(&["explain", "LLL1004"]);
            assert_eq!(exit, 0);
            assert!(
                stdout.contains("LLL1004")
                    && stdout.contains("Unknown non-whitespace primitive atom"),
                "the registered entry is printed: {stdout}"
            );
            assert!(
                !stdout.contains("LLL1005"),
                "exactly one entry is printed: {stdout}"
            );
            let (exit, _, _) = project.cli(&["explain", "LLX9999"]);
            assert_eq!(exit, 2, "unknown codes are CLI misuse");
        }
        // §23.3: sorted result sets with import closure, in every mode.
        "CL-10" => {
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
            for arguments in [
                vec!["--diagnostic-format", "json", "check"],
                vec!["--diagnostic-format", "json", "check", "--all"],
                vec!["--diagnostic-format", "json", "check", "src/Main.lex.tex"],
            ] {
                let (exit, stdout, _) = project.cli(&arguments);
                assert_eq!(exit, 0, "{arguments:?}");
                let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
                let modules: Vec<&str> = value["modules"]
                    .as_array()
                    .expect("modules")
                    .iter()
                    .filter_map(serde_json::Value::as_str)
                    .collect();
                assert_eq!(
                    modules,
                    vec!["Helper", "Main"],
                    "{arguments:?}: sorted with import closure"
                );
            }
        }
        // §23.6: the exact documented exit code per failure class.
        "CL-11" => {
            let config_error = P::example();
            config_error.edit("lexlean.toml", "name = ", "mystery = 1\nname = ");
            let (exit, _, _) = config_error.cli(&["check"]);
            assert_eq!(exit, 2, "configuration errors exit 2");

            let language_error = P::example();
            language_error.edit("src/Main.lex.tex", "natural number", "banana number");
            let (exit, _, _) = language_error.cli(&["check"]);
            assert_eq!(exit, 1, "language errors exit 1");

            let empty_elan = tempfile::tempdir().expect("tempdir");
            let fake = empty_elan.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&fake))], || {
                let environment_error = P::example();
                let (exit, _, _) = environment_error.cli(&["verify"]);
                assert_eq!(exit, 3, "environment errors exit 3");
            });

            let security_error = P::example();
            security_error.edit(
                "lexlean.toml",
                "\n[limits]",
                "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\nurl = \"https://example.invalid/repo.git\"\nrevision = \"0123456789abcdef0123456789abcdef01234567\"\nsubdirectory = \"pkg\"\n\n[limits]",
            );
            let (exit, _, _) = security_error.cli(&["lock"]);
            assert_eq!(exit, 4, "security/network errors exit 4");

            assert_eq!(
                ErrorClass::Internal.exit_code(),
                70,
                "internal failures map to 70"
            );
        }
        // §23.7: exact stream and color discipline in both modes.
        "CL-12" => {
            let failing = P::example();
            failing.edit("src/Main.lex.tex", "natural number", "banana number");
            let (_, stdout, stderr) = failing.cli(&["--diagnostic-format", "json", "check"]);
            assert!(stderr.is_empty(), "JSON mode: empty stderr");
            let value: serde_json::Value =
                serde_json::from_str(&stdout).expect("exactly one JSON object on stdout");
            assert!(value.is_object());
            let (_, human_out, human_err) = failing.cli(&["--color", "never", "check"]);
            assert!(!human_err.is_empty(), "human diagnostics go to stderr");
            assert!(
                !human_out.contains('\u{1b}') && !human_err.contains('\u{1b}'),
                "no ANSI color under --color never"
            );
        }
        // §24.1: the Engine exposes exactly the six stable entry points.
        "CL-13" => {
            let source = api_source();
            let implementation = source
                .split("impl Engine {")
                .nth(1)
                .expect("the Engine impl")
                .split("\n}\n")
                .next()
                .expect("the impl body");
            let mut public: Vec<&str> = implementation
                .lines()
                .filter_map(|line| {
                    line.trim()
                        .strip_prefix("pub fn ")
                        .and_then(|rest| rest.split('(').next())
                })
                .collect();
            public.sort_unstable();
            assert_eq!(
                public,
                vec!["build", "check", "format", "load", "lock", "verify"],
                "§24.1: exactly the six stable entry points are public"
            );
        }
        // §24.4: every multi-module operation returns a set.
        "CL-14" => {
            let project = P::example();
            let checked = project.check_ok();
            assert_eq!(checked.units.len(), 1);
            assert!(
                checked.units.contains_key("Main"),
                "a set even for one module"
            );
            let built = project.build_ok();
            assert!(built.units.contains_key("Main"));
        }
        // §24.3: requests carry no override capability.
        "CL-15" => {
            let source = api_source();
            for (name, expected) in [
                ("CheckRequest", vec!["selection"]),
                ("BuildRequest", vec!["selection"]),
                ("VerifyRequest", vec!["selection"]),
                ("FormatRequest", vec!["selection", "check_only"]),
                ("LockRequest", vec!["check_only", "allow_network"]),
            ] {
                let body = source
                    .split(&format!("pub struct {name} {{"))
                    .nth(1)
                    .unwrap_or_else(|| panic!("{name} exists"))
                    .split('}')
                    .next()
                    .expect("body");
                let fields: Vec<&str> = body
                    .lines()
                    .filter_map(|line| {
                        line.trim()
                            .strip_prefix("pub ")
                            .and_then(|rest| rest.split(':').next())
                    })
                    .collect();
                assert_eq!(
                    fields, expected,
                    "§24.3: {name} has exactly the specified fields"
                );
            }
        }
        // §24.5: every failure is a LexLeanError; no panic on bad input.
        "CL-16" => {
            let nasties: Vec<Vec<u8>> = vec![
                b"\xFF\xFE\x00".to_vec(),
                vec![0u8; 64],
                b"\\begin{lexlean}{Main}".to_vec(),
                [b"\\begin{lexlean}{Main}\n\\title{".to_vec(), vec![b'('; 5000], b"}\n".to_vec()]
                    .concat(),
                b"\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\n\\begin{theorem}{t}\n\\noaxioms\nFor every natural number \\(n\\), \\(n + = n\\).\n\\begin{proof}\nClose the goal by reflexivity.\n\\end{proof}\n\\end{theorem}\n\\end{lexlean}\n".to_vec(),
                b"}{}{}{}{".to_vec(),
            ];
            for (index, bytes) in nasties.iter().enumerate() {
                let project = P::example();
                std::fs::write(project.root.join("src/Main.lex.tex").as_std_path(), bytes)
                    .expect("write");
                let outcome = catch_unwind(AssertUnwindSafe(|| {
                    project
                        .engine()
                        .check(CheckRequest {
                            selection: Selection::Entrypoints,
                        })
                        .err()
                        .map(|error| error.class.exit_code())
                }));
                match outcome {
                    Ok(Some(exit)) => {
                        assert_ne!(
                            exit, 70,
                            "nasty input {index} is a user error, not internal"
                        )
                    }
                    Ok(None) => panic!("nasty input {index} was accepted"),
                    Err(_) => panic!("nasty input {index} caused a panic"),
                }
            }
        }
        // §23.1: environment variables never alter semantics.
        "CL-17" => {
            let baseline = {
                let project = P::example();
                project.build_ok().build_id.expect("built")
            };
            support::with_env(
                &[
                    ("LEXLEAN_MODULE_PREFIX", Some("Hijacked")),
                    ("LEXLEAN_LIMITS", Some("0")),
                    ("LC_ALL", Some("C")),
                ],
                || {
                    let project = P::example();
                    assert_eq!(
                        project.build_ok().build_id.expect("built"),
                        baseline,
                        "environment variables cannot change semantic configuration"
                    );
                },
            );
        }
        // §30.3: the exact version report.
        "CL-18" => {
            let (exit, stdout, _) = support::cli_in(&support::repo_root(), &["--version"]);
            assert_eq!(exit, 0);
            let expected = format!(
                "lexlean {}\nlanguage {}\ncompiler-semantics {}\nlean-toolchain {}\n",
                lexlean::COMPILER_VERSION,
                lexlean::LANGUAGE_VERSION,
                lexlean::compiler_semantics_id().to_hex(),
                lexlean::LEAN_TOOLCHAIN
            );
            assert_eq!(stdout, expected, "§30.3: the exact four-line report");
        }
        other => panic!("no cli-api case is wired for {other}"),
    }
}
