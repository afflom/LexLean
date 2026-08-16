//! The `verification` suite: VR-01..VR-18.

use lexlean::{Selection, VerifyRequest};

use crate::support::{self, P};

/// The names between the first pair of single quotes on an audit line.
fn quoted_name(line: &str) -> String {
    line.split('\'')
        .nth(1)
        .unwrap_or("Demo.M.unknown")
        .to_owned()
}

/// Build a fake elan home whose pinned toolchain mirrors the real one but
/// replaces the named executables with scripts. Returns the fake root.
fn fake_toolchain(replacements: &[(&str, &str)]) -> tempfile::TempDir {
    // Deliberately ignore ELAN_HOME here: concurrent tests may hold the
    // environment lock with a fake value; the real toolchain lives under
    // the home elan directory.
    let real_elan = std::path::PathBuf::from(std::env::var("HOME").expect("HOME")).join(".elan");
    let mangled = lexlean::LEAN_TOOLCHAIN
        .replace('/', "--")
        .replace(':', "---");
    let real_toolchain = real_elan.join("toolchains").join(&mangled);
    let fake = tempfile::Builder::new()
        .prefix("lexlean-fake-elan-")
        .tempdir()
        .expect("tempdir");
    let fake_toolchain_dir = fake.path().join("toolchains").join(&mangled);
    let fake_bin = fake_toolchain_dir.join("bin");
    std::fs::create_dir_all(&fake_bin).expect("mkdir");
    // Mirror everything except bin/ by symlink.
    for entry in std::fs::read_dir(&real_toolchain)
        .expect("real toolchain")
        .flatten()
    {
        if entry.file_name() == "bin" {
            continue;
        }
        std::os::unix::fs::symlink(entry.path(), fake_toolchain_dir.join(entry.file_name()))
            .expect("symlink");
    }
    for entry in std::fs::read_dir(real_toolchain.join("bin"))
        .expect("real bin")
        .flatten()
    {
        let name = entry.file_name().to_string_lossy().into_owned();
        if replacements.iter().any(|(replaced, _)| *replaced == name) {
            continue;
        }
        std::os::unix::fs::symlink(entry.path(), fake_bin.join(&name)).expect("symlink");
    }
    for (name, script) in replacements {
        let path = fake_bin.join(name);
        std::fs::write(&path, script).expect("script");
        let mut permissions = std::fs::metadata(&path).expect("stat").permissions();
        std::os::unix::fs::PermissionsExt::set_mode(&mut permissions, 0o755);
        std::fs::set_permissions(&path, permissions).expect("chmod");
    }
    fake
}

fn process_records(dir: &camino::Utf8Path) -> Vec<serde_json::Value> {
    support::file_set(dir)
        .into_iter()
        .map(|name| {
            serde_json::from_slice(&std::fs::read(dir.join(name).as_std_path()).expect("read"))
                .expect("a process record parses")
        })
        .collect()
}

pub(crate) fn run(id: &str) {
    match id {
        // §22.1: every stage runs; no suppression option exists.
        "VR-01" => {
            let fixture = support::verified();
            let root = &fixture.outcome.root;
            for evidence in [
                "probe/process.json",
                "audit/process.json",
                "audit/output.txt",
                "build-manifest.json",
                "attestation.json",
            ] {
                assert!(
                    root.join(evidence).as_std_path().exists(),
                    "stage evidence `{evidence}` exists"
                );
            }
            assert!(
                !support::file_set(&root.join("process/lean")).is_empty(),
                "compilation stage evidence"
            );
            assert!(
                !support::file_set(&root.join("process/leanchecker")).is_empty(),
                "replay stage evidence"
            );
            for forbidden in [
                ["verify", "--skip-audit"],
                ["verify", "--no-replay"],
                ["verify", "--output"],
            ] {
                let (exit, _, _) = fixture.project.cli(&forbidden);
                assert_eq!(exit, 2, "verify rejects {forbidden:?}");
            }
        }
        // §22.2: versions and executable hashes checked and recorded.
        "VR-02" => {
            let attestation = &support::verified().attestation;
            for tool in ["lean", "lake", "leanchecker"] {
                let record = &attestation["toolchain"][tool];
                assert!(
                    record["executable_sha256"]
                        .as_str()
                        .is_some_and(|hex| hex.len() == 64),
                    "{tool}: executable hash recorded: {attestation}"
                );
            }
            for tool in ["lean", "lake"] {
                assert!(
                    attestation["toolchain"][tool]["version_output"]
                        .as_str()
                        .is_some_and(|version| version.contains("4.32.1")),
                    "{tool}: pinned version recorded"
                );
            }

            // A wrong-version toolchain fails preflight before use.
            let lying = fake_toolchain(&[(
                "lean",
                "#!/bin/sh\necho Lean \\(version 4.31.0, release\\)\n",
            )]);
            let fake_path = lying.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&fake_path))], || {
                let project = P::example();
                project.verify_fails_with("LLV7001");
            });
        }
        // §22.2: the pinned Lake environment, never updating or fetching.
        "VR-03" => {
            let fixture = support::verified();
            let records = process_records(&fixture.outcome.root.join("process/lean"));
            assert!(!records.is_empty());
            for record in &records {
                let argv: Vec<&str> = record["argv"]
                    .as_array()
                    .expect("argv")
                    .iter()
                    .filter_map(|value| value.as_str())
                    .collect();
                assert_eq!(
                    argv.first(),
                    Some(&"env"),
                    "compilation goes through `lake env`: {argv:?}"
                );
                assert!(argv.contains(&"lean"), "lake env lean execution: {argv:?}");
                for forbidden in ["update", "build", "fetch"] {
                    assert!(!argv.contains(&forbidden), "no `{forbidden}`: {argv:?}");
                }
            }
        }
        // §18.8: the unique reserved probe module.
        "VR-04" => {
            let fixture = support::verified();
            let (probe_name, audit_name) =
                lexlean::verify::reserved_module_names(fixture.outcome.semantic_id);
            let probe_files: Vec<String> = support::file_set(&fixture.outcome.root.join("probe"))
                .into_iter()
                .filter(|name| name.ends_with(".lean"))
                .collect();
            assert_eq!(
                probe_files,
                vec![format!("{probe_name}.lean")],
                "exactly the one reserved probe module"
            );
            assert_ne!(probe_name, audit_name, "probe and audit names are distinct");

            // The probe elaborates universe-polymorphic and numeral-bearing
            // interfaces with real Lean: universes are declared through
            // one `universe` command with entry-index prefixes and LSE
            // numerals print with their inferred type ascription (§18.8).
            let project = support::ext_project(support::UNIQUE_MODULE);
            let (probe, record) = support::probe_lean(
                &project,
                &[
                    "test.ext::eqsymm",
                    "test.ext::zeroadd",
                    "lexlean.std.nat::add",
                ],
            );
            assert!(
                probe.text.contains("universe p1u\n"),
                "alpha-renamed universe declaration: {}",
                probe.text
            );
            assert!(
                probe.text.contains("example : {x0 : Type p1u} → {x1 : x0} → {x2 : x0} → (x3 : Eq x1 x2) → Eq x2 x1 := Eq.symm\n"),
                "the universe-polymorphic interface: {}",
                probe.text
            );
            assert!(
                probe.text.contains(
                    "example : (x0 : Nat) → Eq (Nat.add (0 : Nat) x0) x0 := Nat.zero_add\n"
                ),
                "the numeral prints with its inferred ascription: {}",
                probe.text
            );
            assert!(!probe.text.contains(".{"), "no `example.{{u}}` form");
            assert_eq!(
                record.exit_code, 0,
                "the probe elaborates: {}{}",
                record.stdout, record.stderr
            );
            assert!(record.stdout.trim().is_empty() && record.stderr.trim().is_empty());
            assert_eq!(probe.lines.len(), 3, "one example line per probed entry");

            // A mismatching interface fails and the failing Lean line is
            // attributed to its entry.
            let broken = support::ext_project(support::UNIQUE_MODULE);
            broken.edit(
                "lexicons/test-ext/entries/zeroadd.toml",
                "(app (const lexlean.std.nat::add) (nat 0) (local n))",
                "(app (const lexlean.std.nat::add) (local n) (nat 0))",
            );
            broken.relock();
            let (probe, record) =
                support::probe_lean(&broken, &["test.ext::eqsymm", "test.ext::zeroadd"]);
            assert_ne!(record.exit_code, 0, "the wrong interface fails");
            let messages = lexlean::verify::parse_lean_messages(&format!(
                "{}{}",
                record.stdout, record.stderr
            ));
            assert!(!messages.is_empty(), "Lean reported a located error");
            let attributed: Vec<&str> = messages
                .iter()
                .filter_map(|message| probe.entry_at_line(message.line))
                .map(|row| row.entry.as_str())
                .collect();
            assert_eq!(
                attributed,
                vec!["test.ext::zeroadd"],
                "the failing line names its entry"
            );
        }
        // §22.3: topological compilation with one olean per module.
        "VR-05" => {
            let fixture = support::verified();
            let oleans = support::file_set(&fixture.outcome.root.join("oleans"));
            for unit in fixture.outcome.units.values() {
                let expected = format!("{}.olean", unit.lean_module.replace('.', "/"));
                assert!(
                    oleans.contains(&expected),
                    "{}: every verified module has exactly its olean: {oleans:?}",
                    unit.lean_module
                );
            }
        }
        // §22.3: no ilean artifacts anywhere.
        "VR-06" => {
            let fixture = support::verified();
            for file in support::file_set(&fixture.outcome.root) {
                assert!(
                    !file.ends_with(".ilean"),
                    "no ilean requested or kept: {file}"
                );
            }
        }
        // §22.3: any unexpected output fails verification.
        "VR-07" => {
            let fixture = support::verified();
            let records = process_records(&fixture.outcome.root.join("process/lean"));
            for record in &records {
                assert_eq!(
                    record["stdout"].as_str().map(str::trim),
                    Some(""),
                    "a successful stage produced no unexplained stdout"
                );
                assert_eq!(
                    record["stderr"].as_str().map(str::trim),
                    Some(""),
                    "and no stderr"
                );
            }
            // The enforcement site is registered: LLV7006 is the closed code
            // for it and the verifier emits it.
            let source = std::fs::read_to_string(
                support::repo_root()
                    .join("crates/lexlean/src/verify/mod.rs")
                    .as_std_path(),
            )
            .expect("verify source");
            assert!(
                source.contains("LLV7006"),
                "the warning/unexpected-output rejection is wired"
            );
        }
        // §22.4: separate-process replay for every module, and a replay
        // failure fails verification.
        "VR-08" => {
            let fixture = support::verified();
            let replays = process_records(&fixture.outcome.root.join("process/leanchecker"));
            assert_eq!(
                replays.len(),
                fixture.outcome.units.len(),
                "one replay per generated module"
            );
            for record in &replays {
                assert_eq!(
                    record["exit_code"].as_i64(),
                    Some(0),
                    "every replay succeeded"
                );
            }

            let broken = fake_toolchain(&[("leanchecker", "#!/bin/sh\nexit 1\n")]);
            let fake_path = broken.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&fake_path))], || {
                let project = P::example();
                project.verify_fails_with("LLV7003");
            });
        }
        // §18.9: the audit prints axioms exactly once per declaration.
        "VR-09" => {
            let fixture = support::verified();
            let audit_dir = fixture.outcome.root.join("audit");
            let audit_source = support::file_set(&audit_dir)
                .into_iter()
                .find(|name| name.ends_with(".lean"))
                .map(|name| {
                    std::fs::read_to_string(audit_dir.join(name).as_std_path()).expect("read")
                })
                .expect("the audit module");
            assert_eq!(
                audit_source.matches("#print axioms").count(),
                1,
                "exactly one directive for the one generated declaration"
            );
            assert!(
                audit_source.contains("#print axioms LexLeanExample.Main.add_zero"),
                "the directive names the declaration: {audit_source}"
            );
        }
        // §22.5: the axiom parser accepts and rejects exactly the pinned
        // forms; the committed vectors are the oracle.
        "VR-10" => {
            let accepted = std::fs::read_to_string(
                support::repo_root()
                    .join("tests/golden/axiom-parser/accepted.txt")
                    .as_std_path(),
            )
            .expect("accepted vectors");
            for line in accepted.lines().filter(|line| !line.trim().is_empty()) {
                let expected = vec![quoted_name(line)];
                lexlean::verify::axiom::parse_audit_output(line, &expected)
                    .unwrap_or_else(|error| panic!("accepted vector failed: {line}: {error:?}"));
            }
            let rejected = std::fs::read_to_string(
                support::repo_root()
                    .join("tests/golden/axiom-parser/rejected.txt")
                    .as_std_path(),
            )
            .expect("rejected vectors");
            for line in rejected.lines().filter(|line| !line.trim().is_empty()) {
                let expected = vec![quoted_name(line)];
                assert!(
                    lexlean::verify::axiom::parse_audit_output(line, &expected).is_err(),
                    "rejected vector was accepted: {line}"
                );
            }
        }
        // §22.6: policies enforced exactly and recorded per declaration.
        "VR-11" => {
            let attestation = &support::verified().attestation;
            let declarations = attestation["declarations"].as_array().expect("policy rows");
            let row = declarations
                .iter()
                .find(|row| row["name"].as_str() == Some("LexLeanExample.Main.add_zero"))
                .expect("the example declaration row");
            assert_eq!(row["policy"]["kind"].as_str(), Some("none"));
            assert_eq!(
                row["observed"].as_array().map(Vec::len),
                Some(0),
                "an empty observed set under \\noaxioms"
            );

            // A sufficient allow-list verifies and records the observed set.
            let _guard = support::env_lock();
            let allowed = support::em_project("\\allowaxioms{Classical.choice;Quot.sound;propext}");
            let outcome = allowed
                .engine()
                .verify(VerifyRequest {
                    selection: Selection::Entrypoints,
                })
                .expect("a sufficient allow-list verifies");
            let attestation: serde_json::Value = serde_json::from_slice(
                &std::fs::read(outcome.root.join("attestation.json").as_std_path())
                    .expect("attestation"),
            )
            .expect("parses");
            let observed: Vec<&str> = attestation["declarations"][0]["observed"]
                .as_array()
                .expect("observed")
                .iter()
                .filter_map(|value| value.as_str())
                .collect();
            assert_eq!(
                observed,
                vec!["Classical.choice", "Quot.sound", "propext"],
                "the observed set is recorded sorted"
            );
        }
        // §22.7: the exact output normalization rules.
        "VR-12" => {
            let normalizer = lexlean::verify::child::Normalizer::new(
                camino::Utf8Path::new("/tmp/stage-1"),
                camino::Utf8Path::new("/work/project"),
                camino::Utf8Path::new("/work/project/lake"),
                camino::Utf8Path::new("/opt/toolchain"),
            );
            let raw = b"/tmp/stage-1/audit/A.lean:1: note\r\n/work/project/src fine\n/opt/toolchain/bin/lean ok\ntrailing   \n\n\n";
            let normalized = normalizer.normalize(raw);
            assert!(normalized.contains("$STAGING/audit/A.lean"), "{normalized}");
            assert!(normalized.contains("$PROJECT/src"), "{normalized}");
            assert!(normalized.contains("$TOOLCHAIN/bin/lean"), "{normalized}");
            assert!(!normalized.contains('\r'), "CRLF normalizes to LF");
            assert!(
                normalized.contains("trailing\n"),
                "trailing spaces are removed: {normalized:?}"
            );
            assert!(
                !normalized.ends_with("\n\n"),
                "blank tails collapse: {normalized:?}"
            );
        }
        // §22.8: the complete fixed verified artifact set.
        "VR-13" => {
            let fixture = support::verified();
            let files = support::file_set(&fixture.outcome.root);
            type Matcher = Box<dyn Fn(&str) -> bool>;
            let patterns: Vec<(&str, Matcher)> = vec![
                (
                    "attestation.json",
                    Box::new(|f: &str| f == "attestation.json"),
                ),
                (
                    "build-manifest.json",
                    Box::new(|f: &str| f == "build-manifest.json"),
                ),
                (
                    "modules/*.lean",
                    Box::new(|f: &str| f.starts_with("modules/") && f.ends_with(".lean")),
                ),
                (
                    "modules/*.tex",
                    Box::new(|f: &str| f.starts_with("modules/") && f.ends_with(".tex")),
                ),
                (
                    "maps/*.map.json",
                    Box::new(|f: &str| f.starts_with("maps/") && f.ends_with(".map.json")),
                ),
                (
                    "coverage/*.coverage.json",
                    Box::new(|f: &str| f.starts_with("coverage/") && f.ends_with(".coverage.json")),
                ),
                (
                    "lexicons/*.closure.json",
                    Box::new(|f: &str| f.starts_with("lexicons/") && f.ends_with(".closure.json")),
                ),
                (
                    "oleans/*.olean",
                    Box::new(|f: &str| f.starts_with("oleans/") && f.ends_with(".olean")),
                ),
                (
                    "probe/*.lean",
                    Box::new(|f: &str| f.starts_with("probe/") && f.ends_with(".lean")),
                ),
                (
                    "probe/process.json",
                    Box::new(|f: &str| f == "probe/process.json"),
                ),
                (
                    "audit/*.lean",
                    Box::new(|f: &str| f.starts_with("audit/") && f.ends_with(".lean")),
                ),
                (
                    "audit/output.txt",
                    Box::new(|f: &str| f == "audit/output.txt"),
                ),
                (
                    "audit/process.json",
                    Box::new(|f: &str| f == "audit/process.json"),
                ),
                (
                    "process/lean/*.json",
                    Box::new(|f: &str| f.starts_with("process/lean/")),
                ),
                (
                    "process/leanchecker/*.json",
                    Box::new(|f: &str| f.starts_with("process/leanchecker/")),
                ),
            ];
            for file in &files {
                assert!(
                    patterns.iter().any(|(_, matches)| matches(file)),
                    "§22.8: `{file}` is outside the fixed artifact set"
                );
            }
            for (pattern, matches) in &patterns {
                assert!(
                    files.iter().any(|file| matches(file)),
                    "§22.8: the `{pattern}` slot is populated"
                );
            }
        }
        // §22.9: the attestation ID is computed over the body without its
        // own field.
        "VR-14" => {
            let fixture = support::verified();
            let bytes = std::fs::read(fixture.outcome.root.join("attestation.json").as_std_path())
                .expect("attestation bytes");
            let parsed =
                lexlean::artifact::canonical_json::Json::parse(&bytes).expect("canonical JSON");
            let lexlean::artifact::canonical_json::Json::Obj(mut object) = parsed else {
                panic!("an attestation is an object")
            };
            let recorded = object
                .remove("attestation_id")
                .expect("the attestation carries its ID");
            let body = lexlean::artifact::canonical_json::Json::Obj(object).to_canonical_string();
            let recomputed = lexlean::artifact::content_id::attestation_id(&body);
            let lexlean::artifact::canonical_json::Json::Str(recorded_hex) = recorded else {
                panic!("the ID is a string")
            };
            assert_eq!(recomputed.to_hex(), recorded_hex, "§22.9 recomputation");
            assert_eq!(
                fixture.outcome.root.file_name(),
                Some(recorded_hex.as_str()),
                "the directory is the attestation ID"
            );
            assert!(!body.contains("timestamp"), "no timestamp is hashed");
        }
        // §22.1: a failed stage removes staging and publishes nothing.
        "VR-15" => {
            let (project, _error) = support::broken_proof();
            let verified_root = project.root.join(".lexlean/verified");
            if verified_root.as_std_path().exists() {
                let leftovers = support::file_set(&verified_root);
                assert!(
                    leftovers.is_empty(),
                    "a failed verification leaves no staging or artifacts: {leftovers:?}"
                );
            }
        }
        // §5.4: imported-theorem axioms stay subject to the policy.
        "VR-16" => {
            let (_, error) = support::axioms_insufficient();
            support::expect_code(error, "LLV7005");
            let rendered = format!("{error}");
            for axiom in ["propext", "Quot.sound"] {
                assert!(
                    rendered.contains(axiom),
                    "the observed excess from the imported theorem is reported: {rendered}"
                );
            }
        }
        // §22.2: workspace hashes must match the lock; deps must be local.
        "VR-17" => {
            let project = P::example();
            project.edit(
                "lakefile.toml",
                "name = \"nat_add_zero_host\"",
                "name = \"renamed_host\"",
            );
            let error = project
                .engine()
                .verify(VerifyRequest {
                    selection: Selection::Entrypoints,
                })
                .err()
                .expect("a drifted workspace fails preflight");
            assert!(
                error
                    .diagnostics
                    .iter()
                    .any(|d| matches!(d.code.as_str(), "LLV7007" | "LLC0102")),
                "found {:?}",
                error
                    .diagnostics
                    .iter()
                    .map(|d| d.code.as_str())
                    .collect::<Vec<_>>()
            );
        }
        // §5.3: check and build never claim verified status.
        "VR-18" => {
            let project = P::example();
            let (exit, stdout, _) = project.cli(&["--diagnostic-format", "json", "check"]);
            assert_eq!(exit, 0);
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            assert_ne!(value["status"].as_str(), Some("verified"));
            let (exit, stdout, _) = project.cli(&["--diagnostic-format", "json", "build"]);
            assert_eq!(exit, 0);
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            assert_ne!(value["status"].as_str(), Some("verified"));
            assert!(
                !stdout.contains("kernel-checked"),
                "no kernel claim outside verify"
            );
        }
        other => panic!("no verification case is wired for {other}"),
    }
}
