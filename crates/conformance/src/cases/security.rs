//! The `security` suite: SE-01..SE-12.

use lexlean::LockRequest;

use crate::support::{self, P};

/// Create a local git repository holding a lexicon package, returning its
/// commit hash. `extra` files are committed alongside.
fn git_fixture(extra: &[(&str, &str)]) -> (tempfile::TempDir, String) {
    let repo = tempfile::Builder::new()
        .prefix("lexlean-git-")
        .tempdir()
        .expect("tempdir");
    let write = |relative: &str, content: &str| {
        let path = repo.path().join(relative);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("mkdir");
        }
        std::fs::write(path, content).expect("write");
    };
    write(
        "pkg/lexicon.toml",
        "spec = \"lexlean/lexicon/1\"\npackage = \"test.remote\"\nversion = \"1.0.0\"\nlanguage = \"1.0\"\nimports = [\"lexlean.core@1.0.0\", \"lexlean.std.nat@1.0.0\"]\n",
    );
    write(
        "pkg/entries/probe.toml",
        r#"spec = "lexlean/entry/1"
id = "probe"
category = "term-constant"
signature = "(const lexlean.std.nat::nat)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.zero"

[[form]]
id = "probe"
channel = "both"
surface = "probe"
canonical_source = true
features = []

[render]
math = "(operator-name probe)"
"#,
    );
    for (relative, content) in extra {
        write(relative, content);
    }
    let git = |arguments: &[&str]| {
        let output = std::process::Command::new("git")
            .args(arguments)
            .current_dir(repo.path())
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@t")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@t")
            .output()
            .expect("git runs");
        assert!(
            output.status.success(),
            "git {arguments:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stdout).trim().to_owned()
    };
    git(&["init", "--quiet", "."]);
    git(&["add", "-A"]);
    git(&["commit", "--quiet", "-m", "fixture"]);
    let commit = git(&["rev-parse", "HEAD"]);
    (repo, commit)
}

/// A project configured with the git fixture, plus the insteadOf rewrite
/// pairs that route the HTTPS URL to the local repository.
fn git_project(repo_path: &str, commit: &str) -> (P, Vec<(String, String)>) {
    let project = P::example();
    project.edit(
        "lexlean.toml",
        "\n[limits]",
        &format!(
            "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\nurl = \"https://example.invalid/repo.git\"\nrevision = \"{commit}\"\nsubdirectory = \"pkg\"\n\n[limits]"
        ),
    );
    let env = vec![
        ("GIT_CONFIG_COUNT".to_owned(), "1".to_owned()),
        (
            "GIT_CONFIG_KEY_0".to_owned(),
            format!("url.{repo_path}.insteadOf"),
        ),
        (
            "GIT_CONFIG_VALUE_0".to_owned(),
            "https://example.invalid/repo.git".to_owned(),
        ),
    ];
    (project, env)
}

fn lock_with_network(project: &P) -> Result<(), lexlean::error::LexLeanError> {
    project
        .engine()
        .lock(LockRequest {
            check_only: false,
            allow_network: true,
        })
        .map(|_| ())
}

pub(crate) fn run(id: &str) {
    match id {
        // §25.1: confinement everywhere; symlinks are rejected.
        "SE-01" => {
            let escape = P::example();
            escape.edit(
                "lexlean.toml",
                "build_root = \".lexlean\"",
                "build_root = \"../elsewhere\"",
            );
            let error = lexlean::Engine::load(&escape.root.join("lexlean.toml"))
                .err()
                .expect("an escaping build root is rejected");
            support::expect_code(&error, "LLC0101");

            let linked = P::example();
            std::os::unix::fs::symlink(
                "/etc/hostname",
                linked.root.join("src/Evil.lex.tex").as_std_path(),
            )
            .expect("symlink");
            linked.edit(
                "lexlean.toml",
                "entrypoints = [\"src/Main.lex.tex\"]",
                "entrypoints = [\"src/Evil.lex.tex\", \"src/Main.lex.tex\"]",
            );
            linked.relock();
            linked.check_fails_with("LLS8001");
        }
        // §25.1: special files and filesystem identity conflicts.
        "SE-02" => {
            let project = P::example();
            project.add_package(
                "lexicons/test-fifo",
                "test.fifo",
                &["lexlean.core@1.0.0"],
                &[],
            );
            std::fs::create_dir_all(
                project
                    .root
                    .join("lexicons/test-fifo/entries")
                    .as_std_path(),
            )
            .expect("entries dir");
            let status = std::process::Command::new("mkfifo")
                .arg(
                    project
                        .root
                        .join("lexicons/test-fifo/entries/pipe.toml")
                        .as_std_path(),
                )
                .status()
                .expect("mkfifo runs");
            assert!(status.success());
            let error = project
                .engine()
                .lock(LockRequest {
                    check_only: false,
                    allow_network: false,
                })
                .err()
                .expect("a FIFO in a package tree is rejected");
            support::expect_code(&error, "LLS8001");

            let folded = P::example();
            folded.write("src/MAin.lex.tex", &folded.read("src/Main.lex.tex"));
            folded.edit(
                "lexlean.toml",
                "entrypoints = [\"src/Main.lex.tex\"]",
                "entrypoints = [\"src/MAin.lex.tex\", \"src/Main.lex.tex\"]",
            );
            folded.relock();
            folded.check_fails_with("LLC0104");
        }
        // §25.2: direct argv invocation, never a shell.
        "SE-03" => {
            let fixture = support::verified();
            for dir in ["process/lean", "process/leanchecker"] {
                let record_dir = fixture.outcome.root.join(dir);
                for name in support::file_set(&record_dir) {
                    let record: serde_json::Value = serde_json::from_slice(
                        &std::fs::read(record_dir.join(&name).as_std_path()).expect("read"),
                    )
                    .expect("parses");
                    let argv: Vec<&str> = record["argv"]
                        .as_array()
                        .expect("argv")
                        .iter()
                        .filter_map(|value| value.as_str())
                        .collect();
                    assert!(!argv.is_empty());
                    for argument in &argv {
                        assert!(
                            !matches!(*argument, "sh" | "bash" | "-c"),
                            "{dir}/{name}: no shell involvement: {argv:?}"
                        );
                    }
                }
            }
        }
        // §25.3: network only through lock --allow-network.
        "SE-04" => {
            let project = P::example();
            project.edit(
                "lexlean.toml",
                "\n[limits]",
                "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\nurl = \"https://example.invalid/repo.git\"\nrevision = \"0123456789abcdef0123456789abcdef01234567\"\nsubdirectory = \"pkg\"\n\n[limits]",
            );
            for command in [["check"], ["build"], ["verify"]] {
                let (exit, _, stderr) = project.cli(&command);
                assert_ne!(exit, 0, "{command:?} cannot acquire packages");
                assert!(
                    stderr.contains("LLS8003") || stderr.contains("LLC0102"),
                    "{command:?}: refused without acquisition: {stderr}"
                );
            }
            let (exit, _, _) = project.cli(&["build", "--allow-network"]);
            assert_eq!(exit, 2, "only lock accepts --allow-network");
        }
        // §25.4: the deterministic allow-list child environment.
        "SE-05" => {
            let child_source = std::fs::read_to_string(
                support::repo_root()
                    .join("crates/lexlean/src/verify/child.rs")
                    .as_std_path(),
            )
            .expect("child.rs");
            assert!(
                child_source.contains(".env_clear()"),
                "children start from a cleared environment"
            );
            for pinned in ["NO_COLOR", "C.UTF-8", "GIT_TERMINAL_PROMPT"] {
                assert!(child_source.contains(pinned), "§25.4 pins {pinned}");
            }
            // Recorded output normalizes the home prefix away.
            let fixture = support::verified();
            if let Ok(home) = std::env::var("HOME") {
                for dir in ["process/lean", "process/leanchecker", "probe", "audit"] {
                    let record_dir = fixture.outcome.root.join(dir);
                    for name in support::file_set(&record_dir) {
                        if !name.ends_with(".json") {
                            continue;
                        }
                        let text = std::fs::read_to_string(record_dir.join(&name).as_std_path())
                            .expect("read");
                        assert!(
                            !text.contains(&format!("\"{home}")),
                            "{dir}/{name}: records normalize the home prefix"
                        );
                    }
                }
            }
        }
        // §25.5: explicit limits enforced with checked arithmetic.
        "SE-06" => {
            let tiny = P::example();
            tiny.edit(
                "lexlean.toml",
                "max_primitive_atoms = 2000000",
                "max_primitive_atoms = 10",
            );
            tiny.relock();
            tiny.check_fails_with("LLS8002");

            let overflow = P::example();
            overflow.edit(
                "lexlean.toml",
                "max_file_bytes = 4194304",
                "max_file_bytes = 99999999999999999999999999",
            );
            let error = lexlean::Engine::load(&overflow.root.join("lexlean.toml"))
                .err()
                .expect("an overflowing limit is a checked parse failure");
            support::expect_code(&error, "LLC0101");
        }
        // §25.6: confined staging, removed on success and failure.
        "SE-07" => {
            let project = P::example();
            project.build_ok();
            let failing = P::example();
            failing.edit("src/Main.lex.tex", "natural number", "banana number");
            let _ = failing.check_err();
            for candidate in [&project, &failing] {
                let root = candidate.root.join(".lexlean");
                if !root.as_std_path().exists() {
                    continue;
                }
                for entry in walkdir::WalkDir::new(root.as_std_path())
                    .into_iter()
                    .flatten()
                {
                    let name = entry.file_name().to_string_lossy().into_owned();
                    assert!(
                        !name.starts_with(".tmp") && !name.contains(".staging"),
                        "no staging residue: {name}"
                    );
                }
            }
        }
        // §19.7, §22.2: executables and resources are hash-checked.
        "SE-08" => {
            // The PDF side is checked in TX-09; here the attestation records
            // every toolchain executable hash for the verification side.
            let attestation = &support::verified().attestation;
            for tool in ["lean", "lake", "leanchecker"] {
                let hex = attestation["toolchain"][tool]["executable_sha256"]
                    .as_str()
                    .unwrap_or_else(|| panic!("{tool} hash recorded"));
                assert_eq!(hex.len(), 64, "{tool}: a full SHA-256 is recorded");
            }
            let process_dir = support::verified().outcome.root.join("process/lean");
            for name in support::file_set(&process_dir) {
                let record: serde_json::Value = serde_json::from_slice(
                    &std::fs::read(process_dir.join(&name).as_std_path()).expect("read"),
                )
                .expect("parses");
                assert!(
                    record["executable_sha256"]
                        .as_str()
                        .is_some_and(|hex| hex.len() == 64),
                    "{name}: the executed binary's hash is recorded"
                );
            }
        }
        // §19.7: the provider sees canonical TeX and declared resources
        // only, inside an isolated directory. Exercised as a unit in TX-09;
        // here with one declared resource.
        "SE-09" => {
            let project = P::example();
            project.write("assets/logo.txt", "resource bytes\n");
            let script = "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then exit 0; fi\nname=$(basename \"$3\" .tex)\n{ printf '%%PDF-fake\\n'; ls -A .; } > \"$2/$name.pdf\"\n";
            project.write("tools/fakepdf", script);
            let script_path = project.root.join("tools/fakepdf");
            let mut permissions = std::fs::metadata(script_path.as_std_path())
                .expect("stat")
                .permissions();
            std::os::unix::fs::PermissionsExt::set_mode(&mut permissions, 0o755);
            std::fs::set_permissions(script_path.as_std_path(), permissions).expect("chmod");
            let provider = lexlean::config::PdfProvider {
                program: "tools/fakepdf".to_owned(),
                program_sha256: lexlean::artifact::content_id::Sha256Digest::of(script.as_bytes()),
                version_argv: vec!["--version".to_owned()],
                version_stdout_sha256: lexlean::artifact::content_id::Sha256Digest::of(b"\n"),
                compile_argv: vec![
                    "--outdir".to_owned(),
                    "{out_dir}".to_owned(),
                    "{input}".to_owned(),
                ],
                output: "{stem}.pdf".to_owned(),
                resources: vec!["assets/logo.txt".to_owned()],
            };
            let inner =
                lexlean::project::Project::load(&project.root.join("lexlean.toml")).expect("load");
            let build = support::rendered(&project);
            std::fs::create_dir_all(project.root.join(".lexlean").as_std_path())
                .expect("staging parent");
            let result = lexlean::backend::pdf::run_provider(
                &inner,
                &provider,
                build.modules[0].tex_text.as_bytes(),
                &build.modules[0].lean_module,
                &project.root.join(".lexlean"),
            )
            .expect("the provider runs");
            let mut listing: Vec<String> = String::from_utf8_lossy(&result.pdf_bytes)
                .lines()
                .skip(1)
                .filter(|line| !line.is_empty())
                .map(str::to_owned)
                .collect();
            listing.sort();
            assert_eq!(
                listing,
                vec!["LexLeanExample.Main.tex".to_owned(), "logo.txt".to_owned()],
                "exactly the canonical TeX plus the declared resource"
            );
        }
        // §25.7: internal failures are LLI9001/70, never blamed on input.
        "SE-10" => {
            use lexlean::diagnostic::DiagnosticCode;
            let internal = DiagnosticCode::from_validated(DiagnosticCode::validate("LLI9001"));
            assert_eq!(internal.class().exit_code(), 70);
            // Malformed user input never lands in the internal class.
            let project = P::example();
            project.write("src/Main.lex.tex", "}{}{");
            let error = project.check_err();
            assert_ne!(error.class.exit_code(), 70, "user input is a user error");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .all(|d| d.code.as_str() != "LLI9001"),
                "no internal code for user input"
            );
        }
        // §25.6: no secret values or unrelated file contents in output.
        "SE-11" => {
            support::with_env(&[("LEXLEAN_TEST_SECRET", Some("hunter2-marker"))], || {
                let project = P::example();
                project.edit("src/Main.lex.tex", "natural number", "banana number");
                let (_, stdout, stderr) = project.cli(&["--diagnostic-format", "json", "check"]);
                assert!(
                    !stdout.contains("hunter2-marker") && !stderr.contains("hunter2-marker"),
                    "environment values never leak into diagnostics"
                );
            });
            let peeker = P::example();
            peeker.edit(
                "lexlean.toml",
                "entrypoints = [\"src/Main.lex.tex\"]",
                "entrypoints = [\"/etc/passwd\"]",
            );
            let error = lexlean::Engine::load(&peeker.root.join("lexlean.toml"))
                .err()
                .expect("rejected");
            let rendered = format!("{error}");
            assert!(
                !rendered.contains("root:"),
                "diagnostics never quote unrelated file contents"
            );
        }
        // §11.4: exact 40-hex HTTPS-only git, no submodules or LFS.
        "SE-12" => {
            for (mutation, description) in [
                ("revision = \"abc123\"", "a short revision"),
                ("url = \"http://example.invalid/repo.git\"\nrevision = \"0123456789abcdef0123456789abcdef01234567\"", "plain http"),
                ("url = \"file:///tmp/repo\"\nrevision = \"0123456789abcdef0123456789abcdef01234567\"", "file transport"),
                ("url = \"ssh://git@example.invalid/repo.git\"\nrevision = \"0123456789abcdef0123456789abcdef01234567\"", "ssh transport"),
            ] {
                let project = P::example();
                project.edit(
                    "lexlean.toml",
                    "\n[limits]",
                    &format!(
                        "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\n{mutation}\n\n[limits]"
                    ),
                );
                let text = project.read("lexlean.toml");
                let complete = if text.contains("url = ") {
                    text
                } else {
                    text.replacen(
                        "kind = \"git\"\nrevision",
                        "kind = \"git\"\nurl = \"https://example.invalid/repo.git\"\ncommit",
                        1,
                    )
                };
                project.write("lexlean.toml", &complete);
                let error = lexlean::Engine::load(&project.root.join("lexlean.toml"))
                    .err()
                    .unwrap_or_else(|| panic!("{description} is rejected"));
                support::expect_code(&error, "LLC0101");
            }

            // Acquisition itself: a clean fixture acquires and caches; a
            // submodule-bearing or LFS-bearing fixture is rejected.
            let (clean_repo, clean_commit) = git_fixture(&[]);
            let (project, env) = git_project(&clean_repo.path().to_string_lossy(), &clean_commit);
            let pairs: Vec<(&str, Option<&str>)> = env
                .iter()
                .map(|(key, value)| (key.as_str(), Some(value.as_str())))
                .collect();
            support::with_env(&pairs, || {
                lock_with_network(&project).expect("an exact commit acquires over the rewrite");
            });
            // The cache now satisfies offline resolution.
            project.check_ok();

            let (sub_repo, sub_commit) = git_fixture(&[(
                ".gitmodules",
                "[submodule \"x\"]\n\tpath = x\n\turl = https://example.invalid/x.git\n",
            )]);
            let (sub_project, sub_env) =
                git_project(&sub_repo.path().to_string_lossy(), &sub_commit);
            let sub_pairs: Vec<(&str, Option<&str>)> = sub_env
                .iter()
                .map(|(key, value)| (key.as_str(), Some(value.as_str())))
                .collect();
            support::with_env(&sub_pairs, || {
                let error = lock_with_network(&sub_project).expect_err("submodules are rejected");
                support::expect_code(&error, "LLR3001");
            });

            let (lfs_repo, lfs_commit) = git_fixture(&[(
                ".gitattributes",
                "*.bin filter=lfs diff=lfs merge=lfs -text\n",
            )]);
            let (lfs_project, lfs_env) =
                git_project(&lfs_repo.path().to_string_lossy(), &lfs_commit);
            let lfs_pairs: Vec<(&str, Option<&str>)> = lfs_env
                .iter()
                .map(|(key, value)| (key.as_str(), Some(value.as_str())))
                .collect();
            support::with_env(&lfs_pairs, || {
                let error = lock_with_network(&lfs_project).expect_err("LFS is rejected");
                support::expect_code(&error, "LLR3001");
            });
        }
        other => panic!("no security case is wired for {other}"),
    }
}
