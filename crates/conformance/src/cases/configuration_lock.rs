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

fn lock_update_fails_with(project: &P, code: &str) -> lexlean::LexLeanError {
    let error = project
        .engine()
        .lock(LockRequest {
            check_only: false,
            allow_network: false,
        })
        .err()
        .expect("lock fails");
    support::expect_code(&error, code);
    error
}

fn load_fails_with(project: &P, code: &str) -> lexlean::LexLeanError {
    let error = Engine::load(&project.root.join("lexlean.toml"))
        .err()
        .expect("loading the project fails");
    support::expect_code(&error, code);
    error
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

/// The exact `[pdf]` table used to exercise the lock's provider record.
const PDF_TABLE: &str = "\n[pdf]\nmode = \"external\"\nprogram = \"tools/render\"\nprogram_sha256 = \"0000000000000000000000000000000000000000000000000000000000000000\"\nversion_argv = [\"--version\"]\nversion_stdout_sha256 = \"1111111111111111111111111111111111111111111111111111111111111111\"\ncompile_argv = [\"--outdir\", \"{out_dir}\", \"{input}\"]\noutput = \"{stem}.pdf\"\nresources = [\"assets/a.txt\"]\n";

#[allow(clippy::too_many_lines)]
pub(crate) fn run(id: &str) {
    match id {
        // §10.1: exactly the project/1 schema.
        "CF-01" => {
            let unknown = P::example();
            unknown.edit("lexlean.toml", "name = ", "surprise = 1\nname = ");
            load_fails_with(&unknown, "LLC0101");

            let missing = P::example();
            missing.edit("lexlean.toml", "name = \"nat-add-zero\"\n", "");
            load_fails_with(&missing, "LLC0101");

            let wrong_spec = P::example();
            wrong_spec.edit(
                "lexlean.toml",
                "spec = \"lexlean/project/1\"",
                "spec = \"lexlean/project/2\"",
            );
            load_fails_with(&wrong_spec, "LLC0103");

            // Every field is required, `[pdf]` excepted (§10.1): a config
            // without any `lexicon_source` table is rejected rather than
            // defaulted to an empty array.
            let no_sources = P::example();
            no_sources.edit(
                "lexlean.toml",
                "\n[[lexicon_source]]\npackage = \"lexlean.std.nat\"\nkind = \"builtin\"\n",
                "",
            );
            let error = load_fails_with(&no_sources, "LLC0101");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| d.message.contains("lexicon_source")),
                "the missing key is named: {error}"
            );

            // UTF-8, NFC, LF-terminated (§10.1).
            let crlf = P::example();
            crlf.write(
                "lexlean.toml",
                &crlf.read("lexlean.toml").replace('\n', "\r\n"),
            );
            load_fails_with(&crlf, "LLC0101");
            let no_final_lf = P::example();
            let text = no_final_lf.read("lexlean.toml");
            no_final_lf.write("lexlean.toml", text.trim_end_matches('\n'));
            load_fails_with(&no_final_lf, "LLC0101");
            let non_nfc = P::example();
            non_nfc.edit(
                "lexlean.toml",
                "source_roots = [\"src\"]",
                "source_roots = [\"src\", \"src\u{0065}\u{0301}\"]",
            );
            load_fails_with(&non_nfc, "LLC0101");

            // Distinct roles for distinct files (§10).
            let lock_is_config = P::example();
            lock_is_config.edit(
                "lexlean.toml",
                "lockfile = \"lexlean.lock\"",
                "lockfile = \"lexlean.toml\"",
            );
            load_fails_with(&lock_is_config, "LLC0101");
            let lock_is_entry = P::example();
            lock_is_entry.edit(
                "lexlean.toml",
                "lockfile = \"lexlean.lock\"",
                "lockfile = \"src/Main.lex.tex\"",
            );
            load_fails_with(&lock_is_entry, "LLC0101");
            let build_in_source = P::example();
            build_in_source.edit(
                "lexlean.toml",
                "build_root = \".lexlean\"",
                "build_root = \"src/out\"",
            );
            load_fails_with(&build_in_source, "LLC0101");
            let source_in_build = P::example();
            source_in_build.edit(
                "lexlean.toml",
                "build_root = \".lexlean\"",
                "build_root = \".\"",
            );
            load_fails_with(&source_in_build, "LLC0101");
            let build_is_source = P::example();
            build_is_source.edit(
                "lexlean.toml",
                "build_root = \".lexlean\"",
                "build_root = \"src\"",
            );
            load_fails_with(&build_is_source, "LLC0101");

            // Canonical basic strings escape every control scalar
            // including U+007F.
            assert_eq!(
                lexlean::config::toml_string("a\u{7f}b\u{1}c\"d\\e"),
                "\"a\\u007Fb\\u0001c\\\"d\\\\e\"",
                "control scalars, quotes, and backslashes escape"
            );
        }
        // §10.2: limits are explicit and positive, with no hidden default;
        // `max_diagnostics` is enforced in both output modes.
        "CF-02" => {
            let zero = P::example();
            zero.edit(
                "lexlean.toml",
                "max_file_bytes = 4194304",
                "max_file_bytes = 0",
            );
            load_fails_with(&zero, "LLC0101");

            let absent = P::example();
            absent.edit("lexlean.toml", "max_file_bytes = 4194304\n", "");
            load_fails_with(&absent, "LLC0101");

            // Two nonexistent entrypoints yield two diagnostics; a limit of
            // one keeps the first and appends LLS8002 naming the limit, the
            // configured value, the observed count, and the phase.
            let bounded = P::example();
            bounded.edit(
                "lexlean.toml",
                "entrypoints = [\"src/Main.lex.tex\"]",
                "entrypoints = [\"src/A.lex.tex\", \"src/B.lex.tex\"]",
            );
            bounded.edit(
                "lexlean.toml",
                "max_diagnostics = 256",
                "max_diagnostics = 1",
            );
            bounded.relock();
            let error = bounded.check_err();
            let codes: Vec<&str> = error.diagnostics.iter().map(|d| d.code.as_str()).collect();
            assert_eq!(
                codes,
                vec!["LLC0101", "LLS8002"],
                "the first diagnostic survives and the limit marker follows"
            );
            assert_eq!(
                error.diagnostics[0].message, "entrypoint `src/A.lex.tex` does not exist",
                "the first diagnostic in canonical order is kept"
            );
            let marker = &error.diagnostics[1].message;
            for needle in [
                "max_diagnostics",
                "phase check",
                "configured 1",
                "observed 2",
            ] {
                assert!(marker.contains(needle), "{marker:?} names {needle}");
            }
            assert_eq!(
                error.class.exit_code(),
                4,
                "an exceeded explicit limit is a limit violation (§23.6)"
            );
            let (exit, _, stderr) = bounded.cli(&["--color", "never", "check"]);
            assert_eq!(exit, 4);
            assert_eq!(
                stderr.matches("error[").count(),
                2,
                "human mode prints exactly the retained diagnostics plus the marker: {stderr}"
            );
            let (exit, stdout, stderr) = bounded.cli(&["--diagnostic-format", "json", "check"]);
            assert_eq!(exit, 4);
            assert!(stderr.is_empty());
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            let json_codes: Vec<&str> = value["diagnostics"]
                .as_array()
                .expect("diagnostics")
                .iter()
                .filter_map(|d| d["code"].as_str())
                .collect();
            assert_eq!(json_codes, vec!["LLC0101", "LLS8002"]);
            // The full set passes untouched under a sufficient limit.
            bounded.edit("lexlean.toml", "max_diagnostics = 1", "max_diagnostics = 2");
            bounded.relock();
            let error = bounded.check_err();
            assert_eq!(error.diagnostics.len(), 2);
            assert!(error
                .diagnostics
                .iter()
                .all(|d| d.code.as_str() == "LLC0101"));
        }
        // §10.1, §25.1: configured paths stay inside the project.
        "CF-03" => {
            let escape = P::example();
            escape.edit(
                "lexlean.toml",
                "source_roots = [\"src\"]",
                "source_roots = [\"../src\"]",
            );
            load_fails_with(&escape, "LLC0101");

            let absolute = P::example();
            absolute.edit(
                "lexlean.toml",
                "entrypoints = [\"src/Main.lex.tex\"]",
                "entrypoints = [\"/etc/passwd\"]",
            );
            load_fails_with(&absolute, "LLC0101");

            // A build root whose intermediate component is a symlink is
            // rejected at load (§25.1).
            let linked = P::example();
            let elsewhere = tempfile::tempdir().expect("tempdir");
            support::symlink_any(elsewhere.path(), linked.root.join("out").as_std_path());
            linked.edit(
                "lexlean.toml",
                "build_root = \".lexlean\"",
                "build_root = \"out/inner\"",
            );
            load_fails_with(&linked, "LLS8001");

            // Non-UTF-8 paths are an environment failure (§8.3), never a
            // security violation. Only Unix file names carry arbitrary
            // bytes; Windows names are UTF-16 and cannot express this.
            #[cfg(unix)]
            {
                use std::os::unix::ffi::OsStrExt;
                let project = P::example();
                let bad = std::ffi::OsStr::from_bytes(b"src/Bad\xff.lex.tex");
                std::fs::write(project.root.as_std_path().join(bad), b"x").expect("write");
                let error = project
                    .engine()
                    .check(CheckRequest {
                        selection: Selection::All,
                    })
                    .err()
                    .expect("a non-UTF-8 source path is rejected");
                support::expect_code(&error, "LLV7008");
                assert_eq!(error.class.exit_code(), 3, "environment class");
            }
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
            assert_eq!(
                lexlean::project::discover(&inner).expect("discovers"),
                project.root.join("lexlean.toml"),
                "the nearest regular candidate wins"
            );

            // A symlinked candidate is rejected outright (§23.2) as a
            // security failure, even when its target is a valid config.
            let linked = P::example();
            let nested = linked.root.join("src/inner");
            std::fs::create_dir_all(nested.as_std_path()).expect("mkdir");
            support::symlink_any(
                linked.root.join("lexlean.toml").as_std_path(),
                nested.join("lexlean.toml").as_std_path(),
            );
            let (exit, _, stderr) = support::cli_in(&nested, &["--color", "never", "check"]);
            assert_eq!(exit, 4, "a symlinked candidate is a security failure");
            assert!(stderr.starts_with("error[LLS8001]"), "{stderr}");
            let error = lexlean::project::discover(&nested).expect_err("rejected");
            support::expect_code(&error, "LLS8001");

            // Discovery stops at the filesystem root: a directory with no
            // config anywhere above is CLI misuse.
            let bare = tempfile::tempdir().expect("tempdir");
            let bare_path = camino::Utf8Path::from_path(bare.path()).expect("utf8");
            let error = lexlean::project::discover(bare_path).expect_err("nothing found");
            support::expect_code(&error, "LLC0101");
            let (exit, _, _) = support::cli_in(bare_path, &["check"]);
            assert_eq!(exit, 2);
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

            // `./`-prefixed inputs normalize; the same module given twice
            // under two spellings is a duplicate selection, not collapsed.
            let (exit, stdout, _) =
                project.cli(&["--diagnostic-format", "json", "check", "./src/Main.lex.tex"]);
            assert_eq!(exit, 0, "{stdout}");
            let (exit, _, stderr) = project.cli(&["check", "src/Main.lex.tex", "src/Main.lex.tex"]);
            assert_eq!(exit, 2, "a repeated input is CLI misuse: {stderr}");
            assert!(stderr.contains("LLC0002"), "{stderr}");
            let error = project
                .engine()
                .check(CheckRequest {
                    selection: Selection::Files(
                        [
                            camino::Utf8PathBuf::from("src/Main.lex.tex"),
                            camino::Utf8PathBuf::from("./src/Main.lex.tex"),
                        ]
                        .into_iter()
                        .collect(),
                    ),
                })
                .err()
                .expect("two spellings of one input are a duplicate");
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
            load_fails_with(&mixed, "LLC0101");

            let commitless = P::example();
            commitless.edit(
                "lexlean.toml",
                "\n[limits]",
                "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\nurl = \"https://example.invalid/repo.git\"\n\n[limits]",
            );
            load_fails_with(&commitless, "LLC0101");
        }
        // §11.1, §11.2: the lock is canonical, comment-free, sorted, exact;
        // `lock --check` requires canonical configuration bytes too.
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
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mode = std::fs::metadata(project.root.join("lexlean.lock").as_std_path())
                    .expect("stat")
                    .permissions()
                    .mode()
                    & 0o777;
                assert_eq!(mode, 0o644, "the lock is written with ordinary permissions");
            }

            // A commented, otherwise identical lock is noncanonical.
            project.write("lexlean.lock", &format!("# generated\n{bytes}"));
            lock_check_fails_with(&project, "LLC0102");
            project.write("lexlean.lock", &bytes.replace('\n', "\r\n"));
            lock_check_fails_with(&project, "LLC0102");
            project.write("lexlean.lock", &bytes.replacen("1.0.0", "1.0.1", 1));
            lock_check_fails_with(&project, "LLC0102");
            project.write("lexlean.lock", &bytes);
            let (exit, _, _) = project.cli(&["lock", "--check"]);
            assert_eq!(exit, 0, "restored bytes pass");

            // The configuration must be in canonical serialization for
            // `lock --check` (§10.1); the semantics are unchanged, so
            // `check` still succeeds and the lock is still current.
            let padded = P::example();
            padded.edit("lexlean.toml", "name = ", "name    =   ");
            padded.check_ok();
            lock_check_fails_with(&padded, "LLC0101");
            let reordered = P::example();
            reordered.edit(
                "lexlean.toml",
                "spec = \"lexlean/project/1\"\nname = \"nat-add-zero\"\n",
                "name = \"nat-add-zero\"\nspec = \"lexlean/project/1\"\n",
            );
            reordered.check_ok();
            lock_check_fails_with(&reordered, "LLC0101");
            let (exit, _, _) = P::example().cli(&["lock", "--check"]);
            assert_eq!(exit, 0, "the canonical example passes both checks");

            // The `[pdf]` lock record mirrors the configured provider
            // (§11.1): program, argument vectors, output, hashes, resources.
            let pdf = P::example();
            pdf.write("assets/a.txt", "resource\n");
            pdf.write(
                "lexlean.toml",
                &format!("{}{PDF_TABLE}", pdf.read("lexlean.toml")),
            );
            pdf.relock();
            let lock_text = pdf.read("lexlean.lock");
            let expected_pdf = format!(
                "\n[pdf]\nprogram = \"tools/render\"\nprogram_sha256 = \"{}\"\nversion_argv = [\"--version\"]\nversion_stdout_sha256 = \"{}\"\ncompile_argv = [\"--outdir\", \"{{out_dir}}\", \"{{input}}\"]\noutput = \"{{stem}}.pdf\"\n\n[[pdf.resource]]\npath = \"assets/a.txt\"\nsha256 = \"{}\"\n",
                "0".repeat(64),
                "1".repeat(64),
                hex(&sha2::Sha256::digest(b"resource\n"))
            );
            assert!(
                lock_text.ends_with(&expected_pdf),
                "the lock ends with the exact provider record:\n{lock_text}"
            );
            let parsed = lexlean::api::parse_lock_bytes("lexlean.lock", lock_text.as_bytes())
                .expect("the lock parses");
            assert_eq!(parsed.canonical_bytes(), lock_text.as_bytes(), "round trip");
            let (exit, _, stderr) = pdf.cli(&["lock", "--check"]);
            assert_eq!(exit, 0, "{stderr}");
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
        // §11.5: the exact length-framed sorted-file digest; special files,
        // symlinked package roots, and non-UTF-8 paths are rejected.
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
            let linked_entry = path_package_project();
            support::symlink_any(
                linked_entry.root.join("lexlean.toml").as_std_path(),
                linked_entry
                    .root
                    .join("lexicons/test-extra/entries/link.toml")
                    .as_std_path(),
            );
            lock_update_fails_with(&linked_entry, "LLS8001");

            // A FIFO inside the package tree is rejected (a Unix special
            // file; the §8.3 Windows host has no equivalent in a tree).
            #[cfg(unix)]
            {
                let fifo = path_package_project();
                let status = std::process::Command::new("mkfifo")
                    .arg(
                        fifo.root
                            .join("lexicons/test-extra/entries/pipe.toml")
                            .as_std_path(),
                    )
                    .status()
                    .expect("mkfifo runs");
                assert!(status.success());
                lock_update_fails_with(&fifo, "LLS8001");
            }

            // A non-UTF-8 entry path is an environment failure (§8.3);
            // only Unix file names carry arbitrary bytes.
            #[cfg(unix)]
            {
                use std::os::unix::ffi::OsStrExt;
                let bad = path_package_project();
                let name = std::ffi::OsStr::from_bytes(b"bad\xff.toml");
                std::fs::write(
                    bad.root
                        .join("lexicons/test-extra/entries")
                        .as_std_path()
                        .join(name),
                    b"x",
                )
                .expect("write");
                let error = lock_update_fails_with(&bad, "LLV7008");
                assert_eq!(error.class.exit_code(), 3);
            }

            // The package root itself, or any component of its path, being
            // a symlink escapes the project and is rejected (§25.1), even
            // when the target is a valid package.
            let root_link = P::example();
            let outside = tempfile::tempdir().expect("tempdir");
            let outside_pkg = outside.path().join("pkg");
            std::fs::create_dir_all(outside_pkg.join("entries")).expect("mkdir");
            std::fs::write(
                outside_pkg.join("lexicon.toml"),
                "spec = \"lexlean/lexicon/1\"\npackage = \"test.extra\"\nversion = \"1.0.0\"\nlanguage = \"1.0\"\nimports = [\"lexlean.core@1.0.0\"]\n",
            )
            .expect("write");
            std::fs::create_dir_all(root_link.root.join("lexicons").as_std_path()).expect("mkdir");
            support::symlink_any(
                &outside_pkg,
                root_link.root.join("lexicons/test-extra").as_std_path(),
            );
            root_link.add_lexicon_source("test.extra", "lexicons/test-extra");
            lock_update_fails_with(&root_link, "LLS8001");

            let component_link = P::example();
            support::symlink_any(
                outside.path(),
                component_link.root.join("lexicons").as_std_path(),
            );
            component_link.add_lexicon_source("test.extra", "lexicons/pkg");
            lock_update_fails_with(&component_link, "LLS8001");
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

            // The lock file path itself is a lock input: a symlinked lock,
            // even one pointing at the correct bytes, is rejected (§25.1).
            let linked_lock = P::example();
            let elsewhere = tempfile::tempdir().expect("tempdir");
            let target = elsewhere.path().join("lexlean.lock");
            std::fs::write(&target, linked_lock.read("lexlean.lock")).expect("write");
            std::fs::remove_file(linked_lock.root.join("lexlean.lock").as_std_path())
                .expect("remove");
            support::symlink_any(&target, linked_lock.root.join("lexlean.lock").as_std_path());
            // The lock path is checked when the project loads, so no
            // command (check, lock, lock --check) gets as far as reading
            // or rewriting through the link.
            let error = load_fails_with(&linked_lock, "LLS8001");
            assert_eq!(error.class.exit_code(), 4);
            for arguments in [["lock"].as_slice(), &["lock", "--check"], &["check"]] {
                let (exit, _, stderr) = linked_lock.cli(arguments);
                assert_eq!(exit, 4, "{arguments:?}: {stderr}");
            }
            assert_eq!(
                std::fs::read_to_string(&target).expect("read"),
                P::example().read("lexlean.lock"),
                "the symlink target is untouched"
            );
            assert!(
                std::fs::symlink_metadata(linked_lock.root.join("lexlean.lock").as_std_path())
                    .expect("stat")
                    .file_type()
                    .is_symlink(),
                "the symlink is left in place, its target untouched"
            );
        }
        // §11.4: only locked, locally available dependencies resolve.
        "CF-11" => {
            let project = path_package_project();
            std::fs::remove_dir_all(project.root.join("lexicons/test-extra").as_std_path())
                .expect("remove the locked package source");
            let error = project.check_err();
            support::expect_code(&error, "LLR3001");
            assert_eq!(error.class.exit_code(), 1);
        }
        // §11.4, I15: network only through lock --allow-network.
        "CF-12" => {
            let project = P::example();
            project.edit(
                "lexlean.toml",
                "\n[limits]",
                "\n[[lexicon_source]]\npackage = \"test.remote\"\nkind = \"git\"\nurl = \"https://example.invalid/repo.git\"\nrevision = \"0123456789abcdef0123456789abcdef01234567\"\nsubdirectory = \"pkg\"\n\n[limits]",
            );
            let error = lock_update_fails_with(&project, "LLS8003");
            assert_eq!(error.class.exit_code(), 4);

            let (exit, _, _) = project.cli(&["lock", "--check", "--allow-network"]);
            assert_eq!(
                exit, 2,
                "--check and --allow-network are mutually exclusive"
            );
        }
        // §10.4: exactly one Lake configuration, recorded, matched, and
        // confined.
        "CF-13" => {
            let drift = P::example();
            drift.edit("lakefile.toml", "name = ", "defaultTargets = []\nname = ");
            lock_check_fails_with(&drift, "LLC0102");

            let twin = P::example();
            twin.write("lakefile.lean", "-- a second Lake configuration\n");
            lock_update_fails_with(&twin, "LLC0101");

            // Symlinked Lake configuration or manifest files are rejected
            // (§25.1) even when their targets are the right bytes.
            for pinned in ["lakefile.toml", "lake-manifest.json"] {
                let linked = P::example();
                let elsewhere = tempfile::tempdir().expect("tempdir");
                let target = elsewhere.path().join(pinned);
                std::fs::write(&target, linked.read(pinned)).expect("write");
                std::fs::remove_file(linked.root.join(pinned).as_std_path()).expect("remove");
                support::symlink_any(&target, linked.root.join(pinned).as_std_path());
                lock_update_fails_with(&linked, "LLS8001");
                lock_check_fails_with(&linked, "LLS8001");
                // With the lock left as committed, verification preflight
                // rejects the symlink too.
                let inner = lexlean::project::Project::load(&linked.root.join("lexlean.toml"))
                    .expect("loads");
                let lock = lexlean::api::parse_lock_bytes(
                    "lexlean.lock",
                    linked.read("lexlean.lock").as_bytes(),
                )
                .expect("parses");
                let error = lexlean::verify::workspace::preflight(&inner, &lock)
                    .expect_err("preflight rejects a symlinked pin");
                assert_eq!(error.code.as_str(), "LLS8001", "{}", error.message);
            }
        }
        // §8.2: only leanprover/lean4:v4.32.1, in the configuration, at lock
        // time, and at verification preflight.
        "CF-14" => {
            let config = P::example();
            config.edit(
                "lexlean.toml",
                "lean_toolchain = \"leanprover/lean4:v4.32.1\"",
                "lean_toolchain = \"leanprover/lean4:v4.31.0\"",
            );
            load_fails_with(&config, "LLC0101");

            // The project `lean-toolchain` content must be the exact string
            // (§10.4): relocking refuses, `lock --check` refuses, and
            // verification refuses.
            let pin = P::example();
            pin.write("lean-toolchain", "leanprover/lean4:v4.31.0\n");
            let error = lock_update_fails_with(&pin, "LLC0101");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| d.message.contains("v4.31.0") && d.message.contains("v4.32.1")),
                "the diagnostic names both strings: {error}"
            );
            lock_check_fails_with(&pin, "LLC0101");
            let error = pin.verify_fails_with("LLC0101");
            assert_ne!(error.class.exit_code(), 0);

            // Verification preflight itself checks the content, not just
            // the recorded hash: a lock whose pin row matches the wrong
            // content is still refused with the environment code.
            let inner =
                lexlean::project::Project::load(&pin.root.join("lexlean.toml")).expect("loads");
            let mut lock =
                lexlean::api::parse_lock_bytes("lexlean.lock", pin.read("lexlean.lock").as_bytes())
                    .expect("parses");
            for (path, digest) in &mut lock.workspace_files {
                if path == "lean-toolchain" {
                    *digest = lexlean::Sha256Digest::of(b"leanprover/lean4:v4.31.0\n");
                }
            }
            let error = lexlean::verify::workspace::preflight(&inner, &lock)
                .expect_err("preflight refuses the wrong toolchain content");
            assert_eq!(error.code.as_str(), "LLV7001", "{}", error.message);
            assert_eq!(error.code.class().exit_code(), 3);
            assert!(error.message.contains("v4.31.0"), "{}", error.message);
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
