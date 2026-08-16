//! The `configuration-lock` suite: CF-01..CF-15.

use lexlean::{CheckRequest, Engine, LockRequest, Selection};
use sha2::Digest;

use crate::support::{self, P};

fn lock_check_fails_with(project: &P, code: &str) {
    let error = project
        .engine()
        .lock(LockRequest {
            check_only: true,
            allow_network: false,
        })
        .err()
        .expect("lock --check fails");
    support::expect_code(&error, code);
}

/// A project with a small path lexicon package (no entries used by the
/// module, but locked and digested).
fn path_package_project() -> P {
    let project = P::example();
    project.add_package(
        "lexicons/test-extra",
        "test.extra",
        &["lexlean.core@1.0.0", "lexlean.std.nat@1.0.0"],
        &[("nzz.toml", &support::nzz_entry("Nat.le_refl"))],
    );
    project.relock();
    project
}

pub(crate) fn run(id: &str) {
    match id {
        // §10.1: exactly the project/1 schema.
        "CF-01" => {
            let unknown = P::example();
            unknown.edit("lexlean.toml", "name = ", "surprise = 1\nname = ");
            let error = Engine::load(&unknown.root.join("lexlean.toml"))
                .err()
                .expect("an unknown field is rejected");
            support::expect_code(&error, "LLC0101");

            let missing = P::example();
            missing.edit("lexlean.toml", "name = \"nat-add-zero\"\n", "");
            let error = Engine::load(&missing.root.join("lexlean.toml"))
                .err()
                .expect("a missing required field is rejected");
            support::expect_code(&error, "LLC0101");

            let wrong_spec = P::example();
            wrong_spec.edit(
                "lexlean.toml",
                "spec = \"lexlean/project/1\"",
                "spec = \"lexlean/project/2\"",
            );
            let error = Engine::load(&wrong_spec.root.join("lexlean.toml"))
                .err()
                .expect("an unknown schema tag is rejected");
            support::expect_code(&error, "LLC0103");
        }
        // §10.2: limits are explicit and positive, with no hidden default.
        "CF-02" => {
            let zero = P::example();
            zero.edit(
                "lexlean.toml",
                "max_file_bytes = 4194304",
                "max_file_bytes = 0",
            );
            let error = Engine::load(&zero.root.join("lexlean.toml"))
                .err()
                .expect("a zero limit is rejected");
            support::expect_code(&error, "LLC0101");

            let absent = P::example();
            absent.edit("lexlean.toml", "max_file_bytes = 4194304\n", "");
            let error = Engine::load(&absent.root.join("lexlean.toml"))
                .err()
                .expect("an omitted limit has no hidden default");
            support::expect_code(&error, "LLC0101");
        }
        // §10.1, §25.1: configured paths stay inside the project.
        "CF-03" => {
            let escape = P::example();
            escape.edit(
                "lexlean.toml",
                "source_roots = [\"src\"]",
                "source_roots = [\"../src\"]",
            );
            let error = Engine::load(&escape.root.join("lexlean.toml"))
                .err()
                .expect("a parent-escaping source root is rejected");
            support::expect_code(&error, "LLC0101");

            let absolute = P::example();
            absolute.edit(
                "lexlean.toml",
                "entrypoints = [\"src/Main.lex.tex\"]",
                "entrypoints = [\"/etc/passwd\"]",
            );
            let error = Engine::load(&absolute.root.join("lexlean.toml"))
                .err()
                .expect("an absolute entrypoint is rejected");
            support::expect_code(&error, "LLC0101");
        }
        // §23.2: upward discovery of the nearest valid regular config.
        "CF-04" => {
            let project = P::example();
            let nested = project.root.join("src/deeper");
            std::fs::create_dir_all(nested.as_std_path()).expect("mkdir");
            let (exit, _, stderr) = support::cli_in(&nested, &["check"]);
            assert_eq!(exit, 0, "discovery walks upward: {stderr}");

            // A directory named lexlean.toml is not a regular candidate;
            // discovery skips it and still finds the project config above.
            std::fs::create_dir_all(project.root.join("src/deeper/lexlean.toml").as_std_path())
                .expect("mkdir");
            let inner = project.root.join("src/deeper");
            let (exit, _, stderr) = support::cli_in(&inner, &["check"]);
            assert_eq!(exit, 0, "a directory candidate is skipped: {stderr}");

            // A symlinked candidate is rejected outright (§23.2).
            let linked = P::example();
            let nested = linked.root.join("src/inner");
            std::fs::create_dir_all(nested.as_std_path()).expect("mkdir");
            std::os::unix::fs::symlink(
                linked.root.join("lexlean.toml").as_std_path(),
                nested.join("lexlean.toml").as_std_path(),
            )
            .expect("symlink");
            let (exit, _, _) = support::cli_in(&nested, &["check"]);
            assert_ne!(exit, 0, "a symlinked candidate is rejected");
        }
        // §23.3: selection modes are exclusive and canonicalized.
        "CF-05" => {
            let project = P::example();
            let (exit, _, _) = project.cli(&["check", "--all", "src/Main.lex.tex"]);
            assert_eq!(exit, 2, "--all with explicit inputs is CLI misuse");

            let by_file = project
                .engine()
                .check(CheckRequest {
                    selection: Selection::Files(
                        [project.root.join("src/Main.lex.tex")]
                            .into_iter()
                            .collect(),
                    ),
                })
                .expect("an explicit absolute input canonicalizes");
            let by_entry = project.check_ok();
            assert_eq!(
                by_file.units.keys().collect::<Vec<_>>(),
                by_entry.units.keys().collect::<Vec<_>>(),
                "explicit-file and entrypoint selections canonicalize to the same set"
            );
            let error = project
                .engine()
                .check(CheckRequest {
                    selection: Selection::Files(std::collections::BTreeSet::new()),
                })
                .err()
                .expect("an empty explicit selection is invalid");
            support::expect_code(&error, "LLC0002");
        }
        // §10.1: the three source kinds have disjoint schemas.
        "CF-06" => {
            let mixed = P::example();
            mixed.edit(
                "lexlean.toml",
                "package = \"lexlean.std.nat\"\nkind = \"builtin\"",
                "package = \"lexlean.std.nat\"\nkind = \"builtin\"\npath = \"somewhere\"",
            );
            let error = Engine::load(&mixed.root.join("lexlean.toml"))
                .err()
                .expect("a builtin source with a path is rejected");
            support::expect_code(&error, "LLC0101");

            let commitless = P::example();
            commitless.edit(
                "lexlean.toml",
                "\n[limits]",
                "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\nurl = \"https://example.invalid/repo.git\"\n\n[limits]",
            );
            let error = Engine::load(&commitless.root.join("lexlean.toml"))
                .err()
                .expect("a git source without an exact commit is rejected");
            support::expect_code(&error, "LLC0101");
        }
        // §11.1, §11.2: the lock is canonical, comment-free, sorted, exact.
        "CF-07" => {
            let project = P::example();
            let bytes = project.read("lexlean.lock");
            assert!(!bytes.contains('#'), "the lock is comment-free");
            assert!(bytes.ends_with('\n'), "the lock ends with one LF");
            let package_names: Vec<&str> = bytes
                .lines()
                .filter_map(|line| line.strip_prefix("id = \""))
                .collect();
            let mut sorted = package_names.clone();
            sorted.sort_unstable();
            assert_eq!(package_names, sorted, "lock package rows sort by name");

            let result = project
                .engine()
                .lock(LockRequest {
                    check_only: false,
                    allow_network: false,
                })
                .expect("relock");
            assert!(!result.written, "an up-to-date lock is not rewritten");
            assert_eq!(
                project.read("lexlean.lock"),
                bytes,
                "relocking is idempotent"
            );

            project.write("lexlean.lock", &bytes.replacen("1.0.0", "1.0.1", 1));
            lock_check_fails_with(&project, "LLC0102");
        }
        // §11.3: the complete transitive closure, lexlean.core included.
        "CF-08" => {
            let project = P::example();
            let lock = project.read("lexlean.lock");
            assert!(
                lock.contains("id = \"lexlean.core\""),
                "the lock pins lexlean.core even though only std.nat is configured"
            );
            assert!(
                lock.contains("id = \"lexlean.std.nat\""),
                "the configured package"
            );
            let digests = lock.matches("tree_sha256 = \"").count();
            assert!(digests >= 2, "every locked package carries a tree digest");
        }
        // §11.5: the exact length-framed sorted-file digest; special files
        // are rejected.
        "CF-09" => {
            let project = path_package_project();
            let lock = project.read("lexlean.lock");
            let digest_hex = lock
                .split("id = \"test.extra\"")
                .nth(1)
                .and_then(|rest| rest.split("tree_sha256 = \"").nth(1))
                .and_then(|rest| rest.split('"').next())
                .expect("the path package has a locked digest");

            // Recompute per the §11.5 byte layout.
            let mut files: Vec<(String, Vec<u8>)> = Vec::new();
            let base = project.root.join("lexicons/test-extra");
            files.push((
                "lexicon.toml".to_owned(),
                std::fs::read(base.join("lexicon.toml").as_std_path()).expect("read"),
            ));
            files.push((
                "entries/nzz.toml".to_owned(),
                std::fs::read(base.join("entries/nzz.toml").as_std_path()).expect("read"),
            ));
            files.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
            let mut hasher = sha2::Sha256::new();
            hasher.update(b"lexlean-tree-v1\0");
            for (path, bytes) in &files {
                hasher.update(u32::try_from(path.len()).expect("short path").to_be_bytes());
                hasher.update(path.as_bytes());
                hasher.update((bytes.len() as u64).to_be_bytes());
                hasher.update(bytes);
            }
            let manual = hex(&hasher.finalize());
            assert_eq!(
                manual, digest_hex,
                "§11.5: the locked digest equals the manual layout"
            );

            // A symlink inside the package tree is rejected.
            std::os::unix::fs::symlink(
                project.root.join("lexlean.toml").as_std_path(),
                project
                    .root
                    .join("lexicons/test-extra/entries/link.toml")
                    .as_std_path(),
            )
            .expect("symlink");
            let error = project
                .engine()
                .lock(LockRequest {
                    check_only: false,
                    allow_network: false,
                })
                .err()
                .expect("a symlink in a package tree is rejected");
            support::expect_code(&error, "LLS8001");
        }
        // §11.1: any drift fails lock checking; nothing silently refreshes.
        "CF-10" => {
            let config_drift = P::example();
            let before = config_drift.read("lexlean.lock");
            config_drift.edit(
                "lexlean.toml",
                "max_scope_depth = 1024",
                "max_scope_depth = 512",
            );
            lock_check_fails_with(&config_drift, "LLC0102");
            let error = config_drift.check_err();
            support::expect_code(&error, "LLC0102");
            assert_eq!(
                config_drift.read("lexlean.lock"),
                before,
                "a failed check never rewrites the lock"
            );

            let package_drift = path_package_project();
            let entry_text = package_drift.read("lexicons/test-extra/entries/nzz.toml");
            package_drift.write(
                "lexicons/test-extra/entries/nzz.toml",
                &format!("{entry_text}\n"),
            );
            lock_check_fails_with(&package_drift, "LLC0102");
        }
        // §11.4: only locked, locally available dependencies resolve.
        "CF-11" => {
            let project = path_package_project();
            std::fs::remove_dir_all(project.root.join("lexicons/test-extra").as_std_path())
                .expect("remove the locked package source");
            let error = project.check_err();
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLR3001" | "LLC0102")),
                "a missing locked dependency fails resolution, found {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §11.4, I15: network only through lock --allow-network.
        "CF-12" => {
            let project = P::example();
            project.edit(
                "lexlean.toml",
                "\n[limits]",
                "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\nurl = \"https://example.invalid/repo.git\"\nrevision = \"0123456789abcdef0123456789abcdef01234567\"\nsubdirectory = \"pkg\"\n\n[limits]",
            );
            let error = project
                .engine()
                .lock(LockRequest {
                    check_only: false,
                    allow_network: false,
                })
                .err()
                .expect("an uncached git package needs --allow-network");
            support::expect_code(&error, "LLS8003");

            let (exit, _, _) = project.cli(&["lock", "--check", "--allow-network"]);
            assert_eq!(
                exit, 2,
                "--check and --allow-network are mutually exclusive"
            );
        }
        // §10.4: exactly one Lake configuration, recorded and matched.
        "CF-13" => {
            let drift = P::example();
            drift.edit("lakefile.toml", "name = ", "defaultTargets = []\nname = ");
            lock_check_fails_with(&drift, "LLC0102");

            let twin = P::example();
            twin.write("lakefile.lean", "-- a second Lake configuration\n");
            let error = twin
                .engine()
                .lock(LockRequest {
                    check_only: false,
                    allow_network: false,
                })
                .err()
                .expect("two Lake configurations are rejected");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLC0101" | "LLV7007")),
                "found {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §8.2: only leanprover/lean4:v4.32.1.
        "CF-14" => {
            let config = P::example();
            config.edit(
                "lexlean.toml",
                "lean_toolchain = \"leanprover/lean4:v4.32.1\"",
                "lean_toolchain = \"leanprover/lean4:v4.31.0\"",
            );
            let error = Engine::load(&config.root.join("lexlean.toml"))
                .err()
                .expect("a foreign toolchain string is rejected at configuration");
            support::expect_code(&error, "LLC0101");

            let pin = P::example();
            pin.write("lean-toolchain", "leanprover/lean4:v4.31.0\n");
            lock_check_fails_with(&pin, "LLC0102");
        }
        // §23.3: duplicate logical modules and case-folded collisions.
        "CF-15" => {
            let project = P::example();
            let main = project.read("src/Main.lex.tex");
            project.write("src/MAin.lex.tex", &main);
            project.edit(
                "lexlean.toml",
                "entrypoints = [\"src/Main.lex.tex\"]",
                "entrypoints = [\"src/MAin.lex.tex\", \"src/Main.lex.tex\"]",
            );
            project.relock();
            let error = project.check_err();
            support::expect_code(&error, "LLC0104");
        }
        other => panic!("no configuration-lock case is wired for {other}"),
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
