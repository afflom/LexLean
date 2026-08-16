//! The `security` suite: SE-01..SE-12.

use lexlean::LockRequest;

use crate::support::{self, P};

/// The lexicon manifest and one entry committed by every git fixture.
const FIXTURE_MANIFEST: &str = "spec = \"lexlean/lexicon/1\"\npackage = \"test.remote\"\nversion = \"1.0.0\"\nlanguage = \"1.0\"\nimports = [\"lexlean.core@1.0.0\"]\n";
const FIXTURE_ENTRY: &str = r#"spec = "lexlean/entry/1"
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
"#;

/// The rewritten HTTPS URL every git fixture is configured under.
const FIXTURE_URL: &str = "https://example.invalid/repo.git";

/// Run `git` in a fixture repository (test-side, not the compiler).
fn git_in(repo: &std::path::Path, arguments: &[&str]) -> String {
    let output = std::process::Command::new("git")
        .args(arguments)
        .current_dir(repo)
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
}

/// Create a local git repository holding a lexicon package, returning its
/// commit hash. `extra` files are committed alongside; `after_add` runs
/// between `git add` and the commit for fixtures that need index surgery.
fn git_fixture(
    extra: &[(&str, &str)],
    after_add: impl FnOnce(&std::path::Path),
) -> (tempfile::TempDir, String) {
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
    write("pkg/lexicon.toml", FIXTURE_MANIFEST);
    write("pkg/entries/probe.toml", FIXTURE_ENTRY);
    for (relative, content) in extra {
        write(relative, content);
    }
    git_in(repo.path(), &["init", "--quiet", "."]);
    git_in(repo.path(), &["add", "-A"]);
    after_add(repo.path());
    git_in(repo.path(), &["commit", "--quiet", "-m", "fixture"]);
    let commit = git_in(repo.path(), &["rev-parse", "HEAD"]);
    (repo, commit)
}

/// A project configured with a git source at `commit` under the fixture
/// URL and the given subdirectory.
fn git_project(commit: &str, subdirectory: &str) -> P {
    let project = P::example();
    project.edit(
        "lexlean.toml",
        "\n[limits]",
        &format!(
            "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\nurl = \"{FIXTURE_URL}\"\nrevision = \"{commit}\"\nsubdirectory = \"{subdirectory}\"\n\n[limits]"
        ),
    );
    project
}

/// A `git` wrapper on an explicit path that routes the fixture URL to a
/// local repository through argv (`-c url.<repo>.insteadOf=<url>`), so no
/// `GIT_CONFIG_*` environment leaks into the compiler's child. The wrapper
/// directory goes first on `PATH`, which is the one platform variable the
/// compiler retains for executable resolution (§25.4).
struct GitWrapper {
    _dir: tempfile::TempDir,
    path_value: String,
}

fn git_wrapper(local_repo: &std::path::Path) -> GitWrapper {
    let dir = tempfile::Builder::new()
        .prefix("lexlean-gitwrap-")
        .tempdir()
        .expect("tempdir");
    let real_git = String::from_utf8_lossy(
        &std::process::Command::new("sh")
            .args(["-c", "command -v git"])
            .output()
            .expect("sh")
            .stdout,
    )
    .trim()
    .to_owned();
    assert!(!real_git.is_empty(), "git is available for the fixture");
    let script = format!(
        "#!/bin/sh\nexec \"{real_git}\" -c \"url.{}.insteadOf={FIXTURE_URL}\" \"$@\"\n",
        local_repo.display()
    );
    let wrapper = dir.path().join("git");
    std::fs::write(&wrapper, script).expect("write");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).expect("chmod");
    }
    let path_value = format!(
        "{}:{}",
        dir.path().display(),
        std::env::var("PATH").unwrap_or_default()
    );
    GitWrapper {
        _dir: dir,
        path_value,
    }
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

/// Acquire through the wrapper, returning the outcome.
fn acquire_through(
    repo: &std::path::Path,
    project: &P,
) -> Result<(), lexlean::error::LexLeanError> {
    let wrapper = git_wrapper(repo);
    support::with_env(&[("PATH", Some(&wrapper.path_value))], || {
        lock_with_network(project)
    })
}

/// A recording stub executable that prints its environment (sorted) and
/// its argv to stdout, then exits with the code in `$LEXLEAN_STUB_EXIT` if
/// set, else 0.
fn recording_stub(dir: &std::path::Path) -> camino::Utf8PathBuf {
    let path = dir.join("stub");
    std::fs::write(
        &path,
        "#!/bin/sh\nenv | LC_ALL=C sort\nprintf 'ARGV:%s\\n' \"$@\"\nprintf 'CWD:%s\\n' \"$(pwd)\"\n",
    )
    .expect("write");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).expect("chmod");
    }
    camino::Utf8PathBuf::from_path_buf(path).expect("utf8")
}

#[allow(clippy::too_many_lines)]
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

            #[cfg(unix)]
            {
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
                let error = linked.check_fails_with("LLS8001");
                assert!(
                    error
                        .diagnostics
                        .iter()
                        .all(|d| !d.message.contains(linked.root.as_str())),
                    "diagnostics name project-relative paths: {error}"
                );
                // A symlinked source *directory* component is rejected too.
                let dir_link = P::example();
                let outside = tempfile::tempdir().expect("tempdir");
                std::fs::write(
                    outside.path().join("Main.lex.tex"),
                    dir_link.read("src/Main.lex.tex"),
                )
                .expect("write");
                std::fs::remove_dir_all(dir_link.root.join("src").as_std_path()).expect("rm");
                std::os::unix::fs::symlink(outside.path(), dir_link.root.join("src").as_std_path())
                    .expect("symlink");
                dir_link.check_fails_with("LLS8001");
            }
        }
        // §25.1: special files and filesystem identity conflicts.
        "SE-02" => {
            #[cfg(unix)]
            {
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
            }

            let folded = P::example();
            folded.write("src/MAin.lex.tex", &folded.read("src/Main.lex.tex"));
            folded.edit(
                "lexlean.toml",
                "entrypoints = [\"src/Main.lex.tex\"]",
                "entrypoints = [\"src/MAin.lex.tex\", \"src/Main.lex.tex\"]",
            );
            folded.relock();
            folded.check_fails_with("LLC0104");

            // Two paths naming one file by identity (a hard link) are a
            // filesystem identity conflict (§25.1).
            let hard = P::example();
            std::fs::hard_link(
                hard.root.join("src/Main.lex.tex").as_std_path(),
                hard.root.join("src/Twin.lex.tex").as_std_path(),
            )
            .expect("hard link");
            let error = hard
                .engine()
                .check(lexlean::CheckRequest {
                    selection: lexlean::Selection::All,
                })
                .err()
                .expect("hard-linked twins are rejected");
            support::expect_code(&error, "LLC0104");
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
            // The child runner passes argv elements through verbatim: a
            // shell metacharacter argument reaches the child unexpanded.
            #[cfg(unix)]
            {
                let dir = tempfile::tempdir().expect("tempdir");
                let stub = recording_stub(dir.path());
                let cwd = camino::Utf8Path::from_path(dir.path()).expect("utf8");
                let limits = support::limits_of(&P::example());
                let normalizer = lexlean::verify::child::Normalizer::new(cwd, cwd, cwd, cwd);
                let record = lexlean::verify::child::run(
                    &lexlean::verify::child::ChildSpec {
                        tool: "stub",
                        module: None,
                        program: &stub,
                        executable_sha256: lexlean::Sha256Digest::of(b""),
                        argv: vec!["$HOME; echo pwned".to_owned(), "a b".to_owned()],
                        cwd,
                        extra_env: vec![],
                        toolchain_bin: cwd,
                    },
                    &limits,
                    &normalizer,
                )
                .expect("the stub runs");
                assert!(
                    record.stdout.contains("ARGV:$HOME; echo pwned\nARGV:a b\n"),
                    "argv is not shell-interpreted: {}",
                    record.stdout
                );
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
            for command in [["check"], ["build"], ["verify"], ["fmt"]] {
                let (exit, _, stderr) = project.cli(&command);
                assert_ne!(exit, 0, "{command:?} cannot acquire packages");
                assert!(
                    stderr.contains("LLS8003") || stderr.contains("LLC0102"),
                    "{command:?}: refused without acquisition: {stderr}"
                );
            }
            let (exit, _, _) = project.cli(&["build", "--allow-network"]);
            assert_eq!(exit, 2, "only lock accepts --allow-network");
            // No acquisition means no cache and no git staging anywhere.
            assert!(
                !project.root.join(".lexlean/cache").as_std_path().exists(),
                "nothing was fetched"
            );
        }
        // §25.4: the deterministic allow-list child environment, observed
        // from inside an actual child.
        "SE-05" => {
            #[cfg(unix)]
            {
                let dir = tempfile::tempdir().expect("tempdir");
                let stub = recording_stub(dir.path());
                let cwd = camino::Utf8Path::from_path(dir.path()).expect("utf8");
                let toolchain_bin = camino::Utf8PathBuf::from("/nonexistent/toolchain/bin");
                let limits = support::limits_of(&P::example());
                let normalizer = lexlean::verify::child::Normalizer::new(cwd, cwd, cwd, cwd);
                let record = support::with_env(
                    &[
                        ("LEXLEAN_TEST_SECRET", Some("hunter2-marker")),
                        ("HTTPS_PROXY", Some("http://proxy.invalid")),
                        ("GIT_SSH_COMMAND", Some("ssh -i /secret")),
                        ("GIT_ASKPASS", Some("/usr/bin/askpass")),
                        ("LANG", Some("de_DE.UTF-8")),
                        ("LC_ALL", Some("de_DE.UTF-8")),
                        ("NO_COLOR", None),
                        ("TERM", Some("xterm-256color")),
                    ],
                    || {
                        lexlean::verify::child::run(
                            &lexlean::verify::child::ChildSpec {
                                tool: "stub",
                                module: Some("Probe".to_owned()),
                                program: &stub,
                                executable_sha256: lexlean::Sha256Digest::of(b""),
                                argv: vec!["one".to_owned()],
                                cwd,
                                extra_env: vec![("LEAN_PATH".to_owned(), "x:y".to_owned())],
                                toolchain_bin: &toolchain_bin,
                            },
                            &limits,
                            &normalizer,
                        )
                        .expect("the stub runs")
                    },
                );
                let observed: std::collections::BTreeMap<String, String> = record
                    .stdout
                    .lines()
                    .take_while(|line| !line.starts_with("ARGV:"))
                    .filter_map(|line| line.split_once('='))
                    .map(|(key, value)| (key.to_owned(), value.to_owned()))
                    .collect();
                let mut expected_keys = vec![
                    "GIT_TERMINAL_PROMPT",
                    "HOME",
                    "LANG",
                    "LC_ALL",
                    "LEAN_PATH",
                    "NO_COLOR",
                    "PATH",
                    "PWD",
                ];
                if std::env::var_os("ELAN_HOME").is_some() {
                    expected_keys.push("ELAN_HOME");
                }
                expected_keys.sort_unstable();
                let mut observed_keys: Vec<&str> = observed
                    .keys()
                    .map(String::as_str)
                    // `sh` itself exports PWD, SHLVL, `_`, and OLDPWD; those
                    // are the shell's, not the compiler's.
                    .filter(|key| !matches!(*key, "SHLVL" | "_" | "OLDPWD"))
                    .collect();
                observed_keys.sort_unstable();
                assert_eq!(
                    observed_keys, expected_keys,
                    "exactly the allow-list environment reaches the child: {observed:?}"
                );
                assert_eq!(observed["NO_COLOR"], "1");
                assert_eq!(observed["LANG"], "C.UTF-8");
                assert_eq!(observed["LC_ALL"], "C.UTF-8");
                assert_eq!(observed["GIT_TERMINAL_PROMPT"], "0");
                assert_eq!(observed["LEAN_PATH"], "x:y");
                assert!(
                    observed["PATH"].starts_with("/nonexistent/toolchain/bin:"),
                    "the toolchain bin directory leads PATH: {}",
                    observed["PATH"]
                );
                assert!(!record.stdout.contains("hunter2-marker"));
                assert!(record.stdout.contains("ARGV:one\n"));
                assert_eq!(record.module.as_deref(), Some("Probe"));
                assert_eq!(record.exit_code, 0);
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
        // §25.5: explicit limits enforced with checked arithmetic, for
        // parsing and for child processes.
        "SE-06" => {
            let tiny = P::example();
            tiny.edit(
                "lexlean.toml",
                "max_primitive_atoms = 2000000",
                "max_primitive_atoms = 10",
            );
            tiny.relock();
            let error = tiny.check_fails_with("LLS8002");
            assert_eq!(error.class.exit_code(), 4);

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

            // Child output and time caps: the extreme configured values
            // never overflow, and an exceeded cap names the tool, phase,
            // limit, configured value, and observed value.
            #[cfg(unix)]
            {
                let dir = tempfile::tempdir().expect("tempdir");
                let cwd = camino::Utf8Path::from_path(dir.path()).expect("utf8");
                let normalizer = lexlean::verify::child::Normalizer::new(cwd, cwd, cwd, cwd);
                let mut limits = support::limits_of(&P::example());
                let talker = dir.path().join("talker");
                std::fs::write(
                    &talker,
                    "#!/bin/sh\nhead -c 4096 /dev/zero | tr '\\0' 'x'\n",
                )
                .expect("write");
                let sleeper = dir.path().join("sleeper");
                std::fs::write(&sleeper, "#!/bin/sh\nsleep 30\n").expect("write");
                for script in [&talker, &sleeper] {
                    use std::os::unix::fs::PermissionsExt;
                    std::fs::set_permissions(script, std::fs::Permissions::from_mode(0o755))
                        .expect("chmod");
                }
                let talker = camino::Utf8PathBuf::from_path_buf(talker).expect("utf8");
                let sleeper = camino::Utf8PathBuf::from_path_buf(sleeper).expect("utf8");
                fn spec<'a>(
                    program: &'a camino::Utf8Path,
                    cwd: &'a camino::Utf8Path,
                ) -> lexlean::verify::child::ChildSpec<'a> {
                    lexlean::verify::child::ChildSpec {
                        tool: "stub",
                        module: Some("Probe".to_owned()),
                        program,
                        executable_sha256: lexlean::Sha256Digest::of(b""),
                        argv: vec![],
                        cwd,
                        extra_env: vec![],
                        toolchain_bin: cwd,
                    }
                }
                limits.max_child_output_bytes = u64::MAX;
                limits.child_timeout_ms = u64::MAX;
                lexlean::verify::child::run(&spec(&talker, cwd), &limits, &normalizer)
                    .expect("extreme limits are checked arithmetic, not overflow");
                limits.max_child_output_bytes = 100;
                let error = lexlean::verify::child::run(&spec(&talker, cwd), &limits, &normalizer)
                    .expect_err("the output cap is enforced");
                assert_eq!(error.code.as_str(), "LLS8002");
                for needle in [
                    "max_child_output_bytes",
                    "`stub`",
                    "phase Probe",
                    "configured 100",
                    "observed at least 101",
                ] {
                    assert!(error.message.contains(needle), "{}", error.message);
                }
                limits.max_child_output_bytes = 1_000_000;
                limits.child_timeout_ms = 200;
                let error = lexlean::verify::child::run(&spec(&sleeper, cwd), &limits, &normalizer)
                    .expect_err("the timeout is enforced");
                assert_eq!(error.code.as_str(), "LLS8002");
                for needle in [
                    "child_timeout_ms",
                    "`stub`",
                    "phase Probe",
                    "configured 200",
                ] {
                    assert!(error.message.contains(needle), "{}", error.message);
                }
            }
        }
        // §25.6: confined staging, removed on success and failure, and
        // never in the project root.
        "SE-07" => {
            let project = P::example();
            project.build_ok();
            let failing = P::example();
            failing.edit("src/Main.lex.tex", "natural number", "banana number");
            let _ = failing.check_err();
            let no_residue = |candidate: &P| {
                for entry in walkdir::WalkDir::new(candidate.root.as_std_path())
                    .into_iter()
                    .flatten()
                {
                    let name = entry.file_name().to_string_lossy().into_owned();
                    assert!(
                        !name.starts_with(".tmp") && !name.contains(".staging"),
                        "no staging residue anywhere under the project: {name}"
                    );
                }
                let mut top: Vec<String> = std::fs::read_dir(candidate.root.as_std_path())
                    .expect("read_dir")
                    .flatten()
                    .map(|entry| entry.file_name().to_string_lossy().into_owned())
                    .collect();
                top.sort();
                for name in &top {
                    assert!(
                        [
                            ".lexlean",
                            "NatAddZeroHost.lean",
                            "lake-manifest.json",
                            "lakefile.toml",
                            "lean-toolchain",
                            "lexlean.lock",
                            "lexlean.toml",
                            "src"
                        ]
                        .contains(&name.as_str()),
                        "the project root gains no files: {name}"
                    );
                }
            };
            no_residue(&project);
            no_residue(&failing);
            // Git acquisition stages under the build root and cleans up.
            let (repo, commit) = git_fixture(&[], |_| {});
            let git = git_project(&commit, "pkg");
            acquire_through(repo.path(), &git).expect("acquires");
            no_residue(&git);
            assert!(
                git.root
                    .join(format!(".lexlean/cache/git/{commit}"))
                    .as_std_path()
                    .is_dir(),
                "the cache is under the build root"
            );
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
                let identity = attestation["toolchain"][tool]["version_output"]
                    .as_str()
                    .unwrap_or_else(|| panic!("{tool} identity recorded"));
                assert!(
                    !identity.trim().is_empty(),
                    "{tool}: a nonempty checked identity"
                );
            }
            assert!(
                attestation["toolchain"]["leanchecker"]["version_output"]
                    .as_str()
                    .is_some_and(|text| text.contains("replays Init.Prelude: exit 0")),
                "leanchecker's identity is a checked replay probe"
            );
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
            #[cfg(unix)]
            {
                let mut permissions = std::fs::metadata(script_path.as_std_path())
                    .expect("stat")
                    .permissions();
                std::os::unix::fs::PermissionsExt::set_mode(&mut permissions, 0o755);
                std::fs::set_permissions(script_path.as_std_path(), permissions).expect("chmod");
            }
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
            const GOOD_URL: &str = "url = \"https://example.invalid/repo.git\"";
            const GOOD_REVISION: &str = "revision = \"0123456789abcdef0123456789abcdef01234567\"";
            const GOOD_SUBDIRECTORY: &str = "subdirectory = \"pkg\"";
            // Each mutation varies exactly one field of an otherwise valid
            // git source.
            for (url, revision, subdirectory, description) in [
                (
                    GOOD_URL,
                    "revision = \"0123456789abcdef0123456789abcdef0123456\"",
                    GOOD_SUBDIRECTORY,
                    "a 39-hex revision",
                ),
                (
                    GOOD_URL,
                    "revision = \"0123456789ABCDEF0123456789abcdef01234567\"",
                    GOOD_SUBDIRECTORY,
                    "an uppercase-hex revision",
                ),
                (
                    GOOD_URL,
                    "revision = \"main\"",
                    GOOD_SUBDIRECTORY,
                    "a mutable reference",
                ),
                (
                    "url = \"http://example.invalid/repo.git\"",
                    GOOD_REVISION,
                    GOOD_SUBDIRECTORY,
                    "plain http",
                ),
                (
                    "url = \"ssh://git@example.invalid/repo.git\"",
                    GOOD_REVISION,
                    GOOD_SUBDIRECTORY,
                    "ssh transport",
                ),
                (
                    "url = \"file:///tmp/repo\"",
                    GOOD_REVISION,
                    GOOD_SUBDIRECTORY,
                    "file transport",
                ),
                (
                    "url = \"git://example.invalid/repo.git\"",
                    GOOD_REVISION,
                    GOOD_SUBDIRECTORY,
                    "the git protocol",
                ),
                (GOOD_URL, GOOD_REVISION, "", "a missing subdirectory"),
                (
                    GOOD_URL,
                    GOOD_REVISION,
                    "subdirectory = \"../pkg\"",
                    "an escaping subdirectory",
                ),
                (
                    GOOD_URL,
                    GOOD_REVISION,
                    "subdirectory = \"/pkg\"",
                    "an absolute subdirectory",
                ),
            ] {
                let project = P::example();
                let mut table = String::from(
                    "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\n",
                );
                for row in [url, revision, subdirectory] {
                    if !row.is_empty() {
                        table.push_str(row);
                        table.push('\n');
                    }
                }
                project.edit("lexlean.toml", "\n[limits]", &format!("{table}\n[limits]"));
                let error = lexlean::Engine::load(&project.root.join("lexlean.toml"))
                    .err()
                    .unwrap_or_else(|| panic!("{description} is rejected"));
                support::expect_code(&error, "LLC0101");
                assert_eq!(
                    error.diagnostics.len(),
                    1,
                    "{description}: exactly the one varied field is diagnosed: {error}"
                );
            }
            // The unmutated source is accepted by configuration.
            let baseline = P::example();
            baseline.edit(
                "lexlean.toml",
                "\n[limits]",
                &format!(
                    "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\n{GOOD_URL}\n{GOOD_REVISION}\n{GOOD_SUBDIRECTORY}\n\n[limits]"
                ),
            );
            lexlean::Engine::load(&baseline.root.join("lexlean.toml"))
                .expect("the well-formed git source is accepted");

            // Acquisition itself: a clean fixture acquires through the
            // wrapper and caches; the cache then satisfies offline use; a
            // second lock does not touch the network.
            let (clean_repo, clean_commit) = git_fixture(&[], |_| {});
            let project = git_project(&clean_commit, "pkg");
            acquire_through(clean_repo.path(), &project)
                .expect("an exact commit acquires over the argv rewrite");
            let cache_dir = project
                .root
                .join(format!(".lexlean/cache/git/{clean_commit}"));
            let cached: Vec<String> = std::fs::read_dir(cache_dir.as_std_path())
                .expect("cache")
                .flatten()
                .map(|entry| entry.file_name().to_string_lossy().into_owned())
                .collect();
            assert_eq!(cached.len(), 1, "one tree-digest directory: {cached:?}");
            assert_eq!(cached[0].len(), 64, "named by tree digest");
            let cached_files = support::file_set(&cache_dir.join(&cached[0]));
            assert_eq!(
                cached_files,
                ["entries/probe.toml", "lexicon.toml"]
                    .into_iter()
                    .map(str::to_owned)
                    .collect(),
                "exactly the participating files are cached"
            );
            project.check_ok();
            let (exit, _, stderr) = project.cli(&["lock", "--check"]);
            assert_eq!(exit, 0, "{stderr}");
            let lock_text = project.read("lexlean.lock");
            assert!(
                lock_text.contains(&format!(
                    "id = \"test.remote\"\nversion = \"1.0.0\"\nkind = \"git\"\nsource = \"{FIXTURE_URL}\"\nrevision = \"{clean_commit}\"\n"
                )),
                "the lock row records the exact URL and commit: {lock_text}"
            );
            // Offline again with a broken wrapper: the cache is enough.
            let broken = tempfile::tempdir().expect("tempdir");
            std::fs::create_dir_all(broken.path().join("nothing")).expect("mkdir");
            acquire_through(&broken.path().join("nothing"), &project)
                .expect("a cached commit needs no fetch");

            // A tampered cache entry is revalidated and refused, never used.
            let tampered_dir = cache_dir.join(&cached[0]);
            std::fs::write(
                tampered_dir.join("entries/probe.toml").as_std_path(),
                "spec = \"lexlean/entry/1\"\n",
            )
            .expect("write");
            let error = project.check_err();
            support::expect_code(&error, "LLS8003");
            assert!(
                error.diagnostics[0].message.contains("not cached"),
                "a tampered entry counts as absent, never as the package: {}",
                error.diagnostics[0].message
            );

            // A remote that cannot be reached is an environment failure,
            // not a language error and not a policy violation.
            let unreachable = git_project(&clean_commit, "pkg");
            let error = acquire_through(&broken.path().join("nothing"), &unreachable)
                .expect_err("an unreachable remote fails acquisition");
            support::expect_code(&error, "LLV7009");
            assert_eq!(error.class.exit_code(), 3);
            for entry in walkdir::WalkDir::new(unreachable.root.as_std_path())
                .into_iter()
                .flatten()
            {
                let name = entry.file_name().to_string_lossy().into_owned();
                assert!(
                    !name.contains(".staging"),
                    "failed acquisition leaves no staging"
                );
            }
            assert!(
                !unreachable
                    .root
                    .join(format!(".lexlean/cache/git/{clean_commit}"))
                    .as_std_path()
                    .exists(),
                "no cache directory is published on failure"
            );

            // A wrong subdirectory in an otherwise reachable commit.
            let wrong_dir = git_project(&clean_commit, "elsewhere");
            let error = acquire_through(clean_repo.path(), &wrong_dir)
                .expect_err("a missing subdirectory is rejected");
            support::expect_code(&error, "LLR3001");

            // Submodules: a real gitlink entry (mode 160000) in the index.
            let (sub_repo, sub_commit) = git_fixture(&[], |repo| {
                let sha = "0123456789abcdef0123456789abcdef01234567";
                git_in(
                    repo,
                    &[
                        "update-index",
                        "--add",
                        "--cacheinfo",
                        &format!("160000,{sha},vendor/dep"),
                    ],
                );
            });
            let sub_project = git_project(&sub_commit, "pkg");
            let error = acquire_through(sub_repo.path(), &sub_project)
                .expect_err("submodules are rejected");
            support::expect_code(&error, "LLR3001");
            assert!(
                error.diagnostics[0].message.contains("submodules"),
                "{}",
                error.diagnostics[0].message
            );

            // Submodules declared by a `.gitmodules` anywhere in the tree.
            let (modfile_repo, modfile_commit) = git_fixture(
                &[(
                    "pkg/deep/.gitmodules",
                    "[submodule \"x\"]\n\tpath = x\n\turl = https://example.invalid/x.git\n",
                )],
                |_| {},
            );
            let error = acquire_through(modfile_repo.path(), &git_project(&modfile_commit, "pkg"))
                .expect_err(".gitmodules is rejected");
            support::expect_code(&error, "LLR3001");

            // LFS: an attributes file anywhere in the tree enabling the
            // filter, or a pointer file under the package.
            let (lfs_repo, lfs_commit) = git_fixture(
                &[(
                    "docs/.gitattributes",
                    "*.bin filter=lfs diff=lfs merge=lfs -text\n",
                )],
                |_| {},
            );
            let error = acquire_through(lfs_repo.path(), &git_project(&lfs_commit, "pkg"))
                .expect_err("LFS attributes are rejected");
            support::expect_code(&error, "LLR3001");
            assert!(error.diagnostics[0].message.contains("LFS"));
            let (pointer_repo, pointer_commit) = git_fixture(
                &[(
                    "pkg/entries/blob.toml",
                    "version https://git-lfs.github.com/spec/v1\noid sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\nsize 12\n",
                )],
                |_| {},
            );
            let error = acquire_through(pointer_repo.path(), &git_project(&pointer_commit, "pkg"))
                .expect_err("LFS pointer files are rejected");
            support::expect_code(&error, "LLR3001");
            assert!(error.diagnostics[0].message.contains("LFS pointer"));
            // A file that merely mentions the filter in a non-attribute
            // position is not LFS.
            let (mention_repo, mention_commit) = git_fixture(
                &[(
                    "notes/.gitattributes",
                    "# filter=lfs is not enabled here\n*.md text\n",
                )],
                |_| {},
            );
            acquire_through(mention_repo.path(), &git_project(&mention_commit, "pkg"))
                .expect("a comment mentioning the filter is not an LFS attribute");

            // Nested repositories: git records an embedded repository as a
            // gitlink, which the index scan rejects before any file is read.
            let (nested_repo, nested_commit) = git_fixture(&[], |repo| {
                std::fs::create_dir_all(repo.join("pkg/inner")).expect("mkdir");
                git_in(&repo.join("pkg/inner"), &["init", "--quiet", "."]);
                std::fs::write(repo.join("pkg/inner/keep"), "x\n").expect("write");
                git_in(&repo.join("pkg/inner"), &["add", "-A"]);
                git_in(
                    &repo.join("pkg/inner"),
                    &["commit", "--quiet", "-m", "inner"],
                );
                git_in(repo, &["add", "-A"]);
            });
            let error = acquire_through(nested_repo.path(), &git_project(&nested_commit, "pkg"))
                .expect_err("a nested repository is rejected");
            support::expect_code(&error, "LLR3001");
        }
        other => panic!("no security case is wired for {other}"),
    }
}
