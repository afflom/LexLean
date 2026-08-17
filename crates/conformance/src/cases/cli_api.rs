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

/// Every string value anywhere inside a JSON document.
fn json_strings<'a>(value: &'a serde_json::Value, out: &mut Vec<&'a str>) {
    match value {
        serde_json::Value::String(text) => out.push(text),
        serde_json::Value::Array(items) => {
            for item in items {
                json_strings(item, out);
            }
        }
        serde_json::Value::Object(map) => {
            for item in map.values() {
                json_strings(item, out);
            }
        }
        _ => {}
    }
}

/// The exact JSON command result of a failing check on a project whose
/// module contains an unknown word, with the diagnostics scanned for any
/// trace of the temporary project directory (§20.6: no absolute paths).
fn assert_no_absolute_paths(project: &P, value: &serde_json::Value) {
    let mut strings = Vec::new();
    json_strings(value, &mut strings);
    for text in strings {
        assert!(
            !text.contains(project.root.as_str()),
            "JSON output must not carry the absolute project path: {text}"
        );
        assert!(
            !text.starts_with('/') || text.starts_with("/build/") || text.starts_with("/verified/"),
            "JSON output must not carry absolute paths: {text}"
        );
    }
}

#[allow(clippy::too_many_lines)]
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
            let (exit, _, stderr) = project.cli(&["--color", "never", "--frobnicate", "check"]);
            assert_eq!(exit, 2, "unknown global options are misuse");
            assert!(
                stderr.starts_with("error[LLC0001]: "),
                "usage errors are the registered LLC0001 diagnostic: {stderr}"
            );
            let (exit, stdout, _) = project.cli(&["--help"]);
            assert_eq!(exit, 0);
            for option in ["--project", "--diagnostic-format", "--color", "--version"] {
                assert!(stdout.contains(option), "--help lists {option}");
            }
            let (exit, _, _) = project.cli(&["--color", "sometimes", "check"]);
            assert_eq!(exit, 2, "an unknown color mode is misuse");
            let (exit, _, _) = project.cli(&["--diagnostic-format", "xml", "check"]);
            assert_eq!(exit, 2, "an unknown diagnostic format is misuse");
            let (exit, _, stderr) = project.cli(&[]);
            assert_eq!(exit, 2, "a command is required");
            assert!(stderr.contains("LLC0001"), "{stderr}");
        }
        // §23.4: init creates the complete canonical skeleton, never
        // overwriting, and the skeleton locks, checks, and verifies with
        // its lock left current.
        "CL-02" => {
            let target = tempfile::tempdir().expect("tempdir");
            let target_path = camino::Utf8Path::from_path(target.path()).expect("utf8");
            let (exit, stdout, stderr) = support::cli_in(
                target_path,
                &["init", ".", "--name", "fresh", "--module-prefix", "Fresh"],
            );
            assert_eq!(exit, 0, "init succeeds in an empty directory: {stderr}");
            assert_eq!(stdout, "initialized .\n", "the path is echoed as given");
            let files = support::file_set(target_path);
            let expected: std::collections::BTreeSet<String> = [
                ".gitignore",
                "FreshHost.lean",
                "lake-manifest.json",
                "lakefile.toml",
                "lean-toolchain",
                "lexlean.lock",
                "lexlean.toml",
                "src/Main.lex.tex",
            ]
            .into_iter()
            .map(str::to_owned)
            .collect();
            assert_eq!(files, expected, "init writes exactly the skeleton");
            let config_bytes =
                std::fs::read(target_path.join("lexlean.toml").as_std_path()).expect("read");
            let engine = Engine::load(&target_path.join("lexlean.toml")).expect("loads");
            let inner =
                lexlean::project::Project::load(&target_path.join("lexlean.toml")).expect("loads");
            assert_eq!(
                config_bytes,
                inner.config.canonical_toml().into_bytes(),
                "init writes the canonical configuration serialization"
            );
            assert_eq!(
                std::fs::read_to_string(target_path.join("lean-toolchain").as_std_path())
                    .expect("read"),
                format!("{}\n", lexlean::LEAN_TOOLCHAIN)
            );
            engine
                .check(CheckRequest {
                    selection: Selection::Entrypoints,
                })
                .expect("the canonical skeleton checks");
            let (exit, _, stderr) = support::cli_in(target_path, &["lock", "--check"]);
            assert_eq!(
                exit, 0,
                "the initial lock is current and canonical: {stderr}"
            );
            let (exit, _, stderr) = support::cli_in(target_path, &["fmt", "--check"]);
            assert_eq!(exit, 0, "the skeleton module is canonical: {stderr}");

            // A real verification runs `lake env`; the manifest init wrote
            // keeps Lake from touching the workspace, so the lock stays
            // current afterwards (§10.4, §22.2).
            if support::lean_backed("CL-02") {
                let manifest_before =
                    std::fs::read(target_path.join("lake-manifest.json").as_std_path())
                        .expect("read");
                let _guard = support::env_lock();
                let (exit, _, stderr) = support::cli_in(target_path, &["verify"]);
                assert_eq!(exit, 0, "the fresh skeleton verifies: {stderr}");
                drop(_guard);
                assert_eq!(
                    std::fs::read(target_path.join("lake-manifest.json").as_std_path())
                        .expect("read"),
                    manifest_before,
                    "verification leaves lake-manifest.json byte-identical"
                );
                let (exit, _, stderr) = support::cli_in(target_path, &["lock", "--check"]);
                assert_eq!(exit, 0, "the lock is still current after verify: {stderr}");
            }

            let (exit, _, _) = support::cli_in(
                target_path,
                &["init", ".", "--name", "again", "--module-prefix", "Again"],
            );
            assert_eq!(exit, 2, "init never overwrites a nonempty destination");

            // Inputs are validated before anything is written; a refused
            // init leaves an absent destination absent.
            let fresh = tempfile::tempdir().expect("tempdir");
            let fresh_path = camino::Utf8Path::from_path(fresh.path()).expect("utf8");
            for (name, prefix) in [("Bad Name", "Ok"), ("ok", "lower"), ("ok", "Ok..Two")] {
                let (exit, _, stderr) = support::cli_in(
                    fresh_path,
                    &["init", "sub", "--name", name, "--module-prefix", prefix],
                );
                assert_eq!(exit, 2, "invalid init inputs are misuse: {name} {prefix}");
                assert!(stderr.contains("LLC0001"), "{stderr}");
                assert!(
                    !fresh_path.join("sub").as_std_path().exists(),
                    "nothing is created for refused inputs"
                );
            }
            let (exit, stdout, _) = support::cli_in(
                fresh_path,
                &["init", "sub", "--name", "ok", "--module-prefix", "Ok"],
            );
            assert_eq!(exit, 0);
            assert_eq!(stdout, "initialized sub\n");
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
        // §23.5: formatting is idempotent and IR-preserving, and rewrites
        // a noncanonical file to exact canonical bytes.
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

            // A noncanonical fixture: CRLF endings, unsorted imports, extra
            // spaces, and an NFD `≠`. The baseline is asserted canonical
            // first (`fmt --check` passes on it), so the expected bytes are
            // an independent oracle rather than the formatter's own output.
            let helper = "\\begin{lexlean}{Helper}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\\end{lexlean}\n";
            let aux = "\\begin{lexlean}{Aux}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{Natural number addition}\n\\end{lexlean}\n";
            let expected_main = support::DEFS_MODULE
                .replacen(
                    "\\useglossary{test.defs@1.0.0}\n",
                    "\\useglossary{test.defs@1.0.0}\n\\importmodule{Aux}\n\\importmodule{Helper}\n",
                    1,
                )
                .replace(
                    "A count is defined as \\(ℕ\\).",
                    "A count is defined as natural number.",
                )
                .replace("\\(k = k\\)", "\\(k ≠ k\\)");
            let direct = support::defs_project();
            direct.write("src/Helper.lex.tex", helper);
            direct.write("src/Aux.lex.tex", aux);
            direct.write("src/Main.lex.tex", &expected_main);
            let (exit, _, stderr) = direct.cli(&["fmt", "--check", "--all"]);
            assert_eq!(exit, 0, "the baseline fixture is canonical: {stderr}");
            let semantic_direct = support::checked_project(&direct).semantic_id;

            let messy = support::defs_project();
            messy.write("src/Helper.lex.tex", &helper.replace('\n', "\r\n"));
            messy.write("src/Aux.lex.tex", aux);
            let messy_main = expected_main
                .replacen(
                    "\\importmodule{Aux}\n\\importmodule{Helper}\n",
                    "\\importmodule{Helper}\n\\importmodule{Aux}\n",
                    1,
                )
                .replace("\\(k ≠ k\\)", "\\(k  =\u{338}  k\\)")
                .replace("For every natural number", "For every  natural  number")
                .replace('\n', "\r\n");
            assert!(messy_main.contains('\u{338}'), "the fixture is NFD");
            messy.write("src/Main.lex.tex", &messy_main);
            let (exit, _, stderr) = messy.cli(&["--color", "never", "fmt", "--check"]);
            assert_eq!(exit, 1, "the messy fixture is not canonical: {stderr}");
            assert!(stderr.starts_with("error[LLL1003]"), "{stderr}");
            let (exit, stdout, stderr) = messy.cli(&["fmt"]);
            assert_eq!(exit, 0, "{stderr}");
            assert_eq!(stdout, "formatted 2 modules\n");
            assert_eq!(
                messy.read("src/Main.lex.tex"),
                expected_main,
                "the exact canonical bytes: sorted imports, single spaces, NFC, LF"
            );
            assert_eq!(messy.read("src/Helper.lex.tex"), helper, "CRLF became LF");
            assert_eq!(
                messy.read("src/Aux.lex.tex"),
                aux,
                "untouched when canonical"
            );
            let (exit, stdout, _) = messy.cli(&["fmt"]);
            assert_eq!(exit, 0);
            assert_eq!(stdout, "formatted 0 modules\n", "a fixed point");
            assert_eq!(messy.read("src/Main.lex.tex"), expected_main);
            let (exit, _, _) = messy.cli(&["fmt", "--check", "--all"]);
            assert_eq!(exit, 0);
            // The linked IR of the formatted project equals the IR of the
            // canonical fixture written directly.
            assert_eq!(
                support::checked_project(&direct)
                    .linked
                    .to_json()
                    .to_canonical_string(),
                support::checked_project(&messy)
                    .linked
                    .to_json()
                    .to_canonical_string(),
                "formatting preserved the linked IR"
            );
            assert_eq!(
                support::checked_project(&messy).semantic_id,
                semantic_direct
            );
            for entry in walkdir::WalkDir::new(messy.root.join(".lexlean").as_std_path())
                .into_iter()
                .flatten()
            {
                let name = entry.file_name().to_string_lossy().into_owned();
                assert!(!name.contains(".staging"), "fmt staging is removed: {name}");
            }
        }
        // §23.4: clean removes exactly the validated build root.
        "CL-08" => {
            let project = P::example();
            project.build_ok();
            project.write("src/keep.txt", "survives\n");
            let (exit, stdout, _) = project.cli(&["clean"]);
            assert_eq!(exit, 0);
            assert_eq!(stdout, "removed .lexlean\n");
            assert!(!project.root.join(".lexlean").as_std_path().exists());
            assert!(project.root.join("src/keep.txt").as_std_path().exists());
            let (exit, stdout, _) = project.cli(&["clean"]);
            assert_eq!(exit, 0, "cleaning an absent build root succeeds");
            assert_eq!(stdout, "nothing to remove: .lexlean does not exist\n");

            // A symlinked build root is refused and its target survives.
            #[cfg(unix)]
            {
                let victim = tempfile::tempdir().expect("tempdir");
                std::fs::write(victim.path().join("precious.txt"), b"data").expect("write");
                std::os::unix::fs::symlink(
                    victim.path(),
                    project.root.join(".lexlean").as_std_path(),
                )
                .expect("symlink");
                let (exit, _, stderr) = project.cli(&["clean"]);
                assert_eq!(exit, 4, "a symlinked build root is refused: {stderr}");
                assert!(
                    victim.path().join("precious.txt").exists(),
                    "the symlink target is untouched"
                );

                // A symlink component above the build root is refused too.
                let nested = P::example();
                nested.edit(
                    "lexlean.toml",
                    "build_root = \".lexlean\"",
                    "build_root = \"out/lexlean\"",
                );
                nested.relock();
                std::fs::remove_dir_all(nested.root.join("out").as_std_path()).expect("rm");
                let elsewhere = tempfile::tempdir().expect("tempdir");
                std::fs::create_dir_all(elsewhere.path().join("lexlean")).expect("mkdir");
                std::fs::write(elsewhere.path().join("lexlean/precious.txt"), b"data")
                    .expect("write");
                std::os::unix::fs::symlink(elsewhere.path(), nested.root.join("out").as_std_path())
                    .expect("symlink");
                let (exit, _, _) = nested.cli(&["clean"]);
                assert_eq!(exit, 4);
                assert!(elsewhere.path().join("lexlean/precious.txt").exists());
            }
        }
        // §23.4: explain prints exactly one registered entry, in both modes.
        "CL-09" => {
            let project = P::example();
            let (exit, stdout, stderr) = project.cli(&["explain", "LLL1004"]);
            assert_eq!(exit, 0);
            assert!(stderr.is_empty());
            let expected = "## `LLL1004` --- Unknown non-whitespace primitive atom\n\nUnknown non-whitespace primitive atom.\n\nClass: `language`. Exit code: 1.\n";
            assert_eq!(stdout, expected, "the exact registered entry");
            let errors_md =
                std::fs::read_to_string(support::repo_root().join("ERRORS.md").as_std_path())
                    .expect("ERRORS.md");
            assert!(
                errors_md.contains(expected.trim_end()),
                "the entry is the generated ERRORS.md entry"
            );
            let (exit, _, stderr) = project.cli(&["--color", "never", "explain", "LLX9999"]);
            assert_eq!(exit, 2, "unknown codes are CLI misuse");
            assert!(stderr.starts_with("error[LLC0001]"), "{stderr}");

            let (exit, stdout, stderr) =
                project.cli(&["--diagnostic-format", "json", "explain", "LLL1004"]);
            assert_eq!(exit, 0);
            assert!(stderr.is_empty());
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            assert_eq!(value["command"], "explain");
            assert_eq!(value["success"], true);
            assert_eq!(
                value["explanation"], expected,
                "JSON carries the entry text"
            );
            let (exit, stdout, stderr) =
                project.cli(&["--diagnostic-format", "json", "explain", "LLX9999"]);
            assert_eq!(exit, 2);
            assert!(stderr.is_empty());
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            assert_eq!(value["exit_code"], 2);
            assert_eq!(value["diagnostics"][0]["code"], "LLC0001");
            assert!(value.get("explanation").is_none());
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
                assert!(
                    value["source_id"]
                        .as_str()
                        .is_some_and(|hex| hex.len() == 64)
                        && value["semantic_id"]
                            .as_str()
                            .is_some_and(|hex| hex.len() == 64),
                    "check reports its source and semantic IDs"
                );
                assert!(value.get("build_id").is_none(), "absent IDs are omitted");
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
        // §23.7, §20.6: exact stream, color, and path discipline in both
        // modes.
        "CL-12" => {
            let failing = P::example();
            failing.edit("src/Main.lex.tex", "natural number", "banana number");
            let (exit, stdout, stderr) = failing.cli(&["--diagnostic-format", "json", "check"]);
            assert_eq!(exit, 1);
            assert!(stderr.is_empty(), "JSON mode: empty stderr");
            let value: serde_json::Value =
                serde_json::from_str(&stdout).expect("exactly one JSON object on stdout");
            assert!(value.is_object());
            let object = value.as_object().expect("object");
            let keys: Vec<&str> = object.keys().map(String::as_str).collect();
            assert_eq!(
                keys,
                vec![
                    "artifacts",
                    "command",
                    "diagnostics",
                    "exit_code",
                    "modules",
                    "spec",
                    "success"
                ],
                "exactly the §20.6 keys, sorted; absent IDs omitted"
            );
            assert_eq!(value["spec"], "lexlean/command-result/1");
            assert_eq!(value["command"], "check");
            assert_eq!(value["success"], false);
            assert_eq!(value["exit_code"], 1);
            assert_eq!(
                value["diagnostics"][0]["primary"]["path"],
                "src/Main.lex.tex"
            );
            assert!(!stdout.contains('\u{1b}'), "no escape sequences in JSON");
            assert_no_absolute_paths(&failing, &value);
            assert_eq!(
                stdout
                    .matches("\"spec\":\"lexlean/command-result/1\"")
                    .count(),
                1,
                "exactly one result object"
            );

            // Usage errors in JSON mode are inside the object; stderr empty.
            let (exit, stdout, stderr) =
                failing.cli(&["--diagnostic-format", "json", "check", "--bogus"]);
            assert_eq!(exit, 2);
            assert!(stderr.is_empty(), "{stderr}");
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            assert_eq!(value["command"], "check");
            assert_eq!(value["diagnostics"][0]["code"], "LLC0001");
            let (exit, stdout, stderr) =
                failing.cli(&["--diagnostic-format=json", "verify", "--fast"]);
            assert_eq!(exit, 2);
            assert!(stderr.is_empty(), "{stderr}");
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            assert_eq!(value["command"], "verify");

            // Security and configuration failures name project-relative
            // paths only, in JSON.
            #[cfg(unix)]
            {
                let linked = P::example();
                std::os::unix::fs::symlink(
                    "/etc/hostname",
                    linked.root.join("src/Evil.lex.tex").as_std_path(),
                )
                .expect("symlink");
                let (exit, stdout, _) =
                    linked.cli(&["--diagnostic-format", "json", "check", "--all"]);
                assert_eq!(exit, 4);
                let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
                assert_eq!(value["diagnostics"][0]["code"], "LLS8001");
                assert!(
                    value["diagnostics"][0]["message"]
                        .as_str()
                        .is_some_and(|m| m.contains("`src/Evil.lex.tex`")),
                    "{value}"
                );
                assert_no_absolute_paths(&linked, &value);
            }
            let stale = P::example();
            stale.edit(
                "lexlean.toml",
                "max_scope_depth = 1024",
                "max_scope_depth = 512",
            );
            let (exit, stdout, _) = stale.cli(&["--diagnostic-format", "json", "build"]);
            assert_eq!(exit, 2);
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            assert_no_absolute_paths(&stale, &value);

            // Human mode: diagnostics to stderr; --color governs SGR.
            let (_, human_out, human_err) = failing.cli(&["--color", "never", "check"]);
            assert!(human_out.is_empty(), "no summary on failure");
            assert!(human_err.starts_with("error[LLL1004]"), "{human_err}");
            assert!(
                !human_out.contains('\u{1b}') && !human_err.contains('\u{1b}'),
                "no ANSI color under --color never"
            );
            assert!(
                !human_err.contains(failing.root.as_str()),
                "human diagnostics use project-relative paths: {human_err}"
            );
            let (_, _, colored) = failing.cli(&["--color", "always", "check"]);
            assert!(
                colored.starts_with("\u{1b}[1;31merror\u{1b}[0m[LLL1004]"),
                "--color always emits SGR: {colored:?}"
            );
            let (_, json_out, json_err) =
                failing.cli(&["--color", "always", "--diagnostic-format", "json", "check"]);
            assert!(
                json_err.is_empty() && !json_out.contains('\u{1b}'),
                "color is ignored for json"
            );
            let (exit, ok_out, ok_err) = P::example().cli(&["--color", "always", "check"]);
            assert_eq!(exit, 0);
            assert!(ok_err.is_empty(), "no diagnostics on success");
            assert!(ok_out.starts_with("checked 1 module ("), "{ok_out}");
        }
        // §24.1: the Engine exposes exactly the six stable entry points, and
        // the crate root re-exports the §24 types.
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
            let lib = std::fs::read_to_string(
                support::repo_root()
                    .join("crates/lexlean/src/lib.rs")
                    .as_std_path(),
            )
            .expect("lib.rs");
            for name in [
                "Engine",
                "Selection",
                "CheckRequest",
                "BuildRequest",
                "VerifyRequest",
                "FormatRequest",
                "LockRequest",
                "ProjectResultSet",
                "CheckedUnit",
                "BuiltUnit",
                "VerifiedProject",
                "LexLeanError",
                "ErrorClass",
                "Diagnostic",
                "Sha256Digest",
            ] {
                assert!(
                    lib.contains(&format!("{name},"))
                        || lib.contains(&format!("{name}}}"))
                        || lib.contains(&format!("{name};")),
                    "lib.rs re-exports {name}"
                );
            }
            // Every module other than the stable three is a hidden internal.
            let mut hidden_expected = 0usize;
            let mut hidden_found = 0usize;
            let mut previous_hidden = false;
            for line in lib.lines() {
                let trimmed = line.trim();
                if let Some(module) = trimmed.strip_prefix("pub mod ") {
                    let module = module
                        .split(|c: char| c == ';' || c == '{' || c.is_whitespace())
                        .next()
                        .unwrap_or("");
                    let stable = matches!(module, "api" | "diagnostic" | "error" | "embedded");
                    if !stable {
                        hidden_expected += 1;
                        if previous_hidden {
                            hidden_found += 1;
                        }
                    }
                }
                previous_hidden = trimmed == "#[doc(hidden)]";
            }
            assert!(hidden_expected >= 10, "the internals are declared");
            assert_eq!(
                hidden_found, hidden_expected,
                "every internal module is #[doc(hidden)]"
            );
            // The stable types are reachable at the crate root by name.
            let _: fn(&camino::Utf8Path) -> Result<lexlean::Engine, lexlean::LexLeanError> =
                lexlean::Engine::load;
            let _ = lexlean::ErrorClass::Language;
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
            // Nasty configuration and lock bytes never panic either.
            for bytes in [
                b"\xFF\xFE".to_vec(),
                b"spec = \"lexlean/project/1\"\n[[lexicon_source]]\n[[lexicon_source]]\n".to_vec(),
                vec![b'['; 10_000],
                b"limits = 5\n".to_vec(),
            ] {
                let project = P::example();
                std::fs::write(project.root.join("lexlean.toml").as_std_path(), &bytes)
                    .expect("write");
                let outcome = catch_unwind(AssertUnwindSafe(|| {
                    Engine::load(&project.root.join("lexlean.toml"))
                        .err()
                        .map(|error| error.class.exit_code())
                }));
                assert!(
                    matches!(outcome, Ok(Some(2))),
                    "nasty configuration is exit 2"
                );
                let project = P::example();
                std::fs::write(project.root.join("lexlean.lock").as_std_path(), &bytes)
                    .expect("write");
                let outcome =
                    catch_unwind(AssertUnwindSafe(|| project.check_err().class.exit_code()));
                assert!(matches!(outcome, Ok(2)), "nasty lock is exit 2");
            }
        }
        // §23.1: environment variables never alter semantics.
        "CL-17" => {
            let baseline = {
                let project = P::example();
                project.build_ok().build_id.expect("built")
            };
            let hijacked = P::example();
            hijacked.write(
                "src/Main.lex.tex",
                &hijacked
                    .read("src/Main.lex.tex")
                    .replace("natural number", "banana number"),
            );
            support::with_env(
                &[
                    ("LEXLEAN_MODULE_PREFIX", Some("Hijacked")),
                    ("LEXLEAN_LIMITS", Some("0")),
                    (
                        "LEXLEAN_PROJECT",
                        Some(hijacked.root.join("lexlean.toml").as_str()),
                    ),
                    ("LEXLEAN_DIAGNOSTIC_FORMAT", Some("json")),
                    ("LC_ALL", Some("C")),
                    ("LANG", Some("de_DE.UTF-8")),
                    ("NO_COLOR", None),
                ],
                || {
                    let project = P::example();
                    assert_eq!(
                        project.build_ok().build_id.expect("built"),
                        baseline,
                        "environment variables cannot change semantic configuration"
                    );
                    // The CLI reads its configuration from argv and the
                    // discovered project only: still human mode, still this
                    // project, still the same result.
                    let (exit, stdout, stderr) = project.cli(&["build"]);
                    assert_eq!(exit, 0, "{stderr}");
                    assert!(
                        stdout.starts_with(&format!(
                            "built 1 module at .lexlean/build/{}",
                            baseline.to_hex()
                        )),
                        "{stdout}"
                    );
                    assert!(stderr.is_empty());
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
