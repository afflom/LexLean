//! The `verification` suite: VR-01..VR-19.

use lexlean::{Selection, VerifyRequest};

use crate::support::{self, P};

/// The names between the first pair of single quotes on an audit line.
fn quoted_name(line: &str) -> String {
    line.split('\'')
        .nth(1)
        .unwrap_or("Demo.M.unknown")
        .to_owned()
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

fn source_tree(root: &std::path::Path) -> std::collections::BTreeMap<String, Vec<u8>> {
    walkdir::WalkDir::new(root)
        .into_iter()
        .flatten()
        .filter(|entry| entry.file_type().is_file())
        .map(|entry| {
            let relative = entry
                .path()
                .strip_prefix(root)
                .expect("source is below its root")
                .to_string_lossy()
                .replace('\\', "/");
            (
                relative,
                std::fs::read(entry.path()).expect("native Atlas source reads"),
            )
        })
        .collect()
}

/// The cases whose assertions need the pinned toolchain (§8.3); every
/// other case is platform independent and runs on every supported host.
const LEAN_BACKED: [&str; 14] = [
    "VR-01", "VR-02", "VR-03", "VR-04", "VR-05", "VR-06", "VR-07", "VR-08", "VR-09", "VR-11",
    "VR-13", "VR-14", "VR-15", "VR-16",
];

pub(crate) fn run(id: &str) {
    if LEAN_BACKED.contains(&id) && !support::lean_backed(id) {
        run_platform_independent(id);
        return;
    }
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
            let lying = support::fake_toolchain(&[(
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
        // §22.3: any unexpected output fails verification: a clean run has
        // none, and a planted warning on module compilation (exit 0) is
        // LLV7006 with nothing published.
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
            let warning = support::fake_toolchain(&[(
                "lake",
                &support::lake_wrapper(
                    "*/lean-src/*.lean",
                    "warning: fixture-planted warning on a successful compilation",
                    "stderr",
                    false,
                ),
            )]);
            let fake_path = warning.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&fake_path))], || {
                let project = P::example();
                let error = project.verify_fails_with("LLV7006");
                assert!(
                    format!("{error}").contains("fixture-planted warning"),
                    "the diagnostic quotes the unexpected output: {error}"
                );
                assert!(
                    support::file_set(&project.root.join(".lexlean/verified")).is_empty(),
                    "nothing is published after a warning"
                );
            });

            // §20.4: a warning is remapped exactly like an error. Lean
            // 4.32.1 prints the unused-variable warning of a lifted
            // universal binder in the named form
            // `path:line:col: warning(name): message`, so the planted
            // message uses that form at the generated binder's own
            // position: the diagnostic must carry the source span of the
            // binder, the generated location as a note, and a note reading
            // the generated name back to its source spelling (§17.8).
            let lean_text = support::lean_text(&support::rendered(&P::example()), "Main");
            let (line, column) = support::lean_position_of(&lean_text, "llv0");
            let located = support::fake_toolchain(&[(
                "lake",
                &support::lake_message_wrapper(
                    &format!(
                        "$STAGING/lean-src/LexLeanExample/Main.lean:{line}:{column}: warning(lean.unusedVariables): Variable name `llv0` is not explicitly referenced."
                    ),
                    0,
                ),
            )]);
            let fake_path = located.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&fake_path))], || {
                let project = P::example();
                let error = project.verify_fails_with("LLV7006");
                let diagnostic = error
                    .diagnostics
                    .iter()
                    .find(|diagnostic| diagnostic.code.as_str() == "LLV7006")
                    .expect("the warning");
                assert!(
                    diagnostic.message.contains("warning lean.unusedVariables"),
                    "the named severity form is kept: {}",
                    diagnostic.message
                );
                let span = diagnostic
                    .primary
                    .as_ref()
                    .expect("a warning carries a source span, exactly like an error");
                let source = project.read("src/Main.lex.tex");
                assert_eq!(
                    &source[span.byte_start..span.byte_end],
                    "n",
                    "the warning points at the binder in the source"
                );
                assert!(
                    diagnostic
                        .notes
                        .iter()
                        .any(|note| note.message.starts_with("generated location: ")),
                    "the generated location is a note: {diagnostic:?}"
                );
                assert!(
                    diagnostic.notes.iter().any(
                        |note| note.message == "generated name `llv0` is the source binder `n`"
                    ),
                    "the generated name is read back to its source spelling: {diagnostic:?}"
                );
                assert!(
                    support::file_set(&project.root.join(".lexlean/verified")).is_empty(),
                    "nothing is published after a warning"
                );
            });
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

            // A leanchecker that answers the fixed identity probe but fails
            // every replay is a replay failure, not a toolchain mismatch.
            let broken = support::fake_toolchain(&[(
                "leanchecker",
                "#!/bin/sh\nif [ \"$1\" = \"LexLeanIdentityProbe\" ]; then echo 'uncaught exception: Could not find any oleans for: LexLeanIdentityProbe' >&2; fi\nexit 1\n",
            )]);
            let fake_path = broken.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&fake_path))], || {
                let project = P::example();
                let error = project.verify_fails_with("LLV7003");
                // A replay failure is about the module it replayed, so it
                // points at that module's source (§20.1), not at the
                // project manifest.
                let primary = error.diagnostics[0]
                    .primary
                    .as_ref()
                    .expect("a replay failure carries a location");
                assert_eq!(
                    primary.path, "src/Main.lex.tex",
                    "the replay failure points at the module source: {primary:?}"
                );
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
            // A record is not a line: the pinned toolchain breaks a long
            // axiom list at its 120-column format width, and the committed
            // wrapped vectors (blank-line separated, one record each) are
            // accepted with exactly the axioms of the unwrapped spelling.
            let wrapped = std::fs::read_to_string(
                support::repo_root()
                    .join("tests/golden/axiom-parser/accepted-wrapped.txt")
                    .as_std_path(),
            )
            .expect("wrapped vectors");
            let records: Vec<&str> = wrapped
                .split("\n\n")
                .map(str::trim_end)
                .filter(|record| !record.is_empty())
                .collect();
            assert!(
                records.iter().any(|record| record.contains('\n')),
                "the wrapped vectors contain a multi-line record: {wrapped}"
            );
            for record in &records {
                let expected = vec![quoted_name(record)];
                let observed = lexlean::verify::axiom::parse_audit_output(record, &expected)
                    .unwrap_or_else(|error| panic!("wrapped vector failed: {record}: {error:?}"));
                assert_eq!(observed.len(), 1, "one record per vector");
            }
            let three = records
                .iter()
                .find(|record| record.contains("even_or_not_and_more_words"))
                .expect("the three-axiom wrapped vector");
            let observed = lexlean::verify::axiom::parse_audit_output(three, &[quoted_name(three)])
                .expect("accepted");
            assert_eq!(
                observed[&quoted_name(three)],
                ["Classical.choice", "Quot.sound", "propext"],
                "a wrapped list yields the same sorted set as an unwrapped one"
            );
            // A record whose list never closes is still malformed, and the
            // rejection names the declaration whose record was expected
            // (§20.1), so `verify` can anchor it at that declaration.
            let failure = lexlean::verify::axiom::parse_audit_output(
                "'Demo.M.cut' depends on axioms: [propext,\n",
                &["Demo.M.cut".to_owned()],
            )
            .expect_err("an unterminated payload is rejected");
            assert_eq!(failure.diagnostic.code.as_str(), "LLV7004");
            assert_eq!(failure.declaration.as_deref(), Some("Demo.M.cut"));
            let mismatch = lexlean::verify::axiom::parse_audit_output(
                "'Demo.M.other' does not depend on any axioms\n",
                &["Demo.M.cut".to_owned()],
            )
            .expect_err("a record for the wrong declaration is rejected");
            assert_eq!(mismatch.declaration.as_deref(), Some("Demo.M.cut"));

            // The pinned toolchain's live `#print axioms` output, in its own
            // (unsorted) order, is accepted and the observed sets come back
            // sorted; an unknown constant's error line is rejected.
            if support::lean_backed("VR-10") {
                let (output, failing) = support::print_axioms_output();
                let expected = vec![
                    "Demo.M.no_ax".to_owned(),
                    "Demo.M.uses_choice".to_owned(),
                    "Demo.M.uses_funext".to_owned(),
                ];
                assert!(
                    output.contains("[propext, Classical.choice, Quot.sound]"),
                    "the toolchain prints its own order: {output}"
                );
                let observed = lexlean::verify::axiom::parse_audit_output(&output, &expected)
                    .unwrap_or_else(|error| panic!("live output rejected: {output}: {error:?}"));
                assert_eq!(observed["Demo.M.no_ax"], Vec::<String>::new());
                assert_eq!(
                    observed["Demo.M.uses_choice"],
                    ["Classical.choice", "Quot.sound", "propext"]
                );
                assert_eq!(observed["Demo.M.uses_funext"], ["Quot.sound"]);
                assert!(
                    lexlean::verify::axiom::parse_audit_output(&failing, &expected).is_err(),
                    "an unknown-constant error line is not an axiom record: {failing}"
                );

                // The pinned toolchain really does wrap: the vectors above
                // are its behavior, not a hand-written shape.
                let live = support::print_axioms_wrapped_output();
                let name =
                    "AVeryLongModulePrefixIndeedYesReallyLong.Main.even_or_not_and_more_words";
                assert!(
                    live.lines().count() > 1,
                    "the pinned toolchain wraps a record wider than its format width: {live:?}"
                );
                let observed =
                    lexlean::verify::axiom::parse_audit_output(&live, &[name.to_owned()])
                        .unwrap_or_else(|error| {
                            panic!("live wrapped output rejected: {live}: {error:?}")
                        });
                assert_eq!(
                    observed[name],
                    ["Classical.choice", "Quot.sound", "propext"]
                );

                // End to end: a project whose declaration name is long
                // enough to wrap its audit record verifies under pinned
                // Lean, through every stage.
                let _guard = support::env_lock();
                let long = support::long_named_em_project();
                let outcome = long
                    .engine()
                    .verify(VerifyRequest {
                        selection: Selection::Entrypoints,
                    })
                    .unwrap_or_else(|error| panic!("a long declaration name verifies: {error:#?}"));
                let audit =
                    std::fs::read_to_string(outcome.root.join("audit/output.txt").as_std_path())
                        .expect("the recorded audit output");
                let lean_name = support::LONG_AXIOM_COMPONENT.replace('-', "_");
                assert!(
                    audit.contains(&format!(
                        "'LexLeanExample.Main.{lean_name}' depends on axioms: [propext,\n"
                    )),
                    "the audit record really is wrapped: {audit}"
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
            assert_eq!(
                attestation["declarations"][0]["policy"]["kind"].as_str(),
                Some("allow")
            );
            drop(_guard);

            // A policy violation is about the declaration that violated it,
            // so its primary location is that declaration's source span
            // (§20.1) rather than the project manifest.
            let (_, violation) = support::axioms_insufficient();
            let primary = violation.diagnostics[0]
                .primary
                .as_ref()
                .expect("a policy violation carries a location");
            assert_eq!(primary.path, "src/Main.lex.tex");
            assert_eq!(
                (primary.line_start, primary.column_start),
                (6, 1),
                "the span opens at the theorem environment: {primary:?}"
            );

            // `exact`: equality succeeds and records the policy; a superset
            // allow-list is a violation (§22.6), both through the CLI
            // fixtures under tests/fixtures/verification.
            let root = support::repo_root();
            let success = crate::fixtures::check(
                &root.join("tests/fixtures/verification/vr-11-exact-success"),
            )
            .unwrap_or_else(|error| panic!("{error}"));
            assert_eq!(success.exit, 0);
            let verified = success.project.root.join(".lexlean/verified");
            let attestation_path = support::file_set(&verified)
                .into_iter()
                .find(|file| file.ends_with("/attestation.json"))
                .map(|file| verified.join(file))
                .expect("the exact-success attestation");
            let exact: serde_json::Value = serde_json::from_slice(
                &std::fs::read(attestation_path.as_std_path()).expect("attestation"),
            )
            .expect("parses");
            let row = &exact["declarations"][0];
            assert_eq!(row["policy"]["kind"].as_str(), Some("exact"));
            assert_eq!(row["result"].as_str(), Some("ok"), "{row}");
            let allowed: Vec<&str> = row["policy"]["axioms"]
                .as_array()
                .expect("allowed set")
                .iter()
                .filter_map(|value| value.as_str())
                .collect();
            let observed: Vec<&str> = row["observed"]
                .as_array()
                .expect("observed set")
                .iter()
                .filter_map(|value| value.as_str())
                .collect();
            assert_eq!(allowed, observed, "exact: O = A");
            let mismatch = crate::fixtures::check(
                &root.join("tests/fixtures/verification/vr-11-exact-mismatch"),
            )
            .unwrap_or_else(|error| panic!("{error}"));
            assert_eq!(mismatch.codes, ["LLV7005"], "exact with a superset fails");
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
            // §30.4: every JSON artifact kind validates against its schema.
            let root = &fixture.outcome.root;
            support::assert_json_file_schema("attestation", &root.join("attestation.json"));
            support::assert_json_file_schema("build-manifest", &root.join("build-manifest.json"));
            for file in &files {
                if file.starts_with("maps/") {
                    support::assert_json_file_schema("source-map", &root.join(file));
                } else if file.starts_with("coverage/") {
                    support::assert_json_file_schema("coverage", &root.join(file));
                }
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
        // §22.1, I11: a failure in any stage (probe, module elaboration,
        // leanchecker replay, axiom audit, policy) removes staging and
        // publishes no verified artifact.
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
            let root = support::repo_root();
            let stages = [
                (
                    "probe",
                    "tests/fixtures/verification/vr-15-probe-failure",
                    "LLT4003",
                ),
                (
                    "module",
                    "tests/negative/lean-elaboration-failure",
                    "LLV7002",
                ),
                (
                    "leanchecker",
                    "tests/negative/leanchecker-failure",
                    "LLV7003",
                ),
                ("audit", "tests/negative/malformed-axiom-output", "LLV7004"),
                ("policy", "tests/negative/axiom-policy-excess", "LLV7005"),
            ];
            for (stage, fixture, code) in stages {
                let observed = crate::fixtures::check(&root.join(fixture))
                    .unwrap_or_else(|error| panic!("{stage}: {error}"));
                assert_eq!(observed.codes, [code], "{stage} stage failure code");
                let lexlean_root = observed.project.root.join(".lexlean");
                let leftovers: Vec<String> = support::file_set(&lexlean_root)
                    .into_iter()
                    .filter(|file| file.starts_with("verified/") || file.contains(".staging-"))
                    .collect();
                assert!(
                    leftovers.is_empty(),
                    "{stage} failure left staging or verified files: {leftovers:?}"
                );
                let residue: Vec<String> =
                    std::fs::read_dir(lexlean_root.join("verified").as_std_path())
                        .into_iter()
                        .flatten()
                        .flatten()
                        .map(|entry| entry.file_name().to_string_lossy().into_owned())
                        .collect();
                assert!(
                    residue.is_empty(),
                    "{stage} failure left {residue:?} under .lexlean/verified"
                );
            }

            // §20.4: a rejection Lean reports in its named form
            // (`error(lean.unknownIdentifier)`, the shape Lean 4.32.1
            // prints) is remapped like any other, not lost to a bare
            // whole-output diagnostic: the failure carries the source span
            // of the token it names and keeps the error name.
            let lean_text = support::lean_text(&support::rendered(&P::example()), "Main");
            let (line, column) = support::lean_position_of(&lean_text, "Nat.add");
            let named = support::fake_toolchain(&[(
                "lake",
                &support::lake_message_wrapper(
                    &format!(
                        "$STAGING/lean-src/LexLeanExample/Main.lean:{line}:{column}: error(lean.unknownIdentifier): Unknown identifier `Nat.add`"
                    ),
                    1,
                ),
            )]);
            let fake_path = named.path().to_string_lossy().into_owned();
            support::with_env(&[("ELAN_HOME", Some(&fake_path))], || {
                let project = P::example();
                let error = project.verify_fails_with("LLV7002");
                let diagnostic = error
                    .diagnostics
                    .iter()
                    .find(|diagnostic| diagnostic.code.as_str() == "LLV7002")
                    .expect("the rejection");
                assert!(
                    diagnostic.message.contains("error lean.unknownIdentifier")
                        && diagnostic.message.contains("Unknown identifier"),
                    "the named severity form is kept: {}",
                    diagnostic.message
                );
                let span = diagnostic
                    .primary
                    .as_ref()
                    .expect("a named error is remapped to its source span");
                let source = project.read("src/Main.lex.tex");
                let spanned = &source[span.byte_start..span.byte_end];
                assert!(
                    spanned.contains('+') && spanned.len() < source.len(),
                    "the span covers the source the applied operator came from, not the whole file: {spanned:?}"
                );
                assert!(
                    support::file_set(&project.root.join(".lexlean/verified")).is_empty(),
                    "nothing is published after a rejection"
                );
            });
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
        // §22.2, §10.4: workspace files must match the lock, and every
        // Lake manifest dependency must be locally available; verification
        // never fetches.
        "VR-17" => {
            let _guard = support::env_lock();
            // A drifted workspace file without relocking is a stale lock.
            let drifted = P::example();
            drifted.edit(
                "lakefile.toml",
                "name = \"nat_add_zero_host\"",
                "name = \"renamed_host\"",
            );
            let error = drifted
                .engine()
                .verify(VerifyRequest {
                    selection: Selection::Entrypoints,
                })
                .err()
                .expect("a drifted workspace fails before Lean runs");
            support::expect_code(&error, "LLC0102");

            // A locked manifest naming a dependency that is not materialized
            // fails the Lake preflight with LLV7007 and publishes nothing.
            // Reaching the Lake preflight means passing the toolchain
            // preflight first, so this half needs the pinned toolchain; the
            // stale-lock half above fails before Lean runs and is asserted on
            // every supported host (§8.3).
            if !support::lean_backed("VR-17") {
                return;
            }
            let unavailable = P::example();
            unavailable.write(
                "lake-manifest.json",
                "{\"version\": \"1.2.0\",\n \"packagesDir\": \".lake/packages\",\n \"packages\": [{\"type\": \"path\", \"name\": \"absent_dep\", \"dir\": \"vendor/absent_dep\", \"inherited\": false, \"manifestFile\": \"lake-manifest.json\"}],\n \"name\": \"nat_add_zero_host\",\n \"lakeDir\": \".lake\",\n \"fixedToolchain\": false}\n",
            );
            unavailable.relock();
            let error = unavailable
                .engine()
                .verify(VerifyRequest {
                    selection: Selection::Entrypoints,
                })
                .err()
                .expect("an unavailable locked dependency fails preflight");
            support::expect_code(&error, "LLV7007");
            assert!(
                format!("{error}").contains("absent_dep"),
                "the diagnostic names the dependency: {error}"
            );
            assert!(
                support::file_set(&unavailable.root.join(".lexlean/verified")).is_empty(),
                "preflight failure publishes nothing"
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
        "VR-19" => {
            let root = support::repo_root();
            let library = root.join("lean/uor-atlas");
            let exporter = root.join("xtask/lean/AtlasOracleExport.lean");
            let source = root.join("examples/uor-atlas/src");
            assert!(
                library.join("lakefile.toml").is_file(),
                "the completed migration oracle is committed as a Lake package"
            );
            assert!(
                exporter.is_file() && source.join("Atlas.lex.tex").is_file(),
                "the semantic exporter and rooted native Atlas source are committed"
            );
            if !support::lean_backed("VR-19") {
                return;
            }
            let bin = support::real_elan_home()
                .join("toolchains")
                .join(support::mangled_toolchain_name())
                .join("bin");
            let built = std::process::Command::new(bin.join("lake"))
                .arg("build")
                .current_dir(&library)
                .output()
                .expect("the pinned lake runs");
            assert!(
                built.status.success(),
                "the migration oracle elaborates: {}",
                String::from_utf8_lossy(&built.stderr)
            );
            let scratch = tempfile::tempdir().expect("temporary export directory");
            let exported = scratch.path().join("src");
            let migrated = std::process::Command::new(bin.join("lake"))
                .args(["env", "lean"])
                .arg(&exporter)
                .current_dir(&library)
                .env("LEXLEAN_ATLAS_EXPORT", &exported)
                .output()
                .expect("the pinned semantic exporter runs");
            assert!(
                migrated.status.success(),
                "the semantic export succeeds: {}{}",
                String::from_utf8_lossy(&migrated.stdout),
                String::from_utf8_lossy(&migrated.stderr)
            );
            assert!(
                source_tree(&exported) == source_tree(source.as_std_path()),
                "every committed native module, type, value, proof and declaration row equals the completed migration oracle"
            );
            let native = source_tree(source.as_std_path());
            assert!(
                native.values().all(|bytes| {
                    let text = String::from_utf8_lossy(bytes);
                    !text.contains("\"imports\":[\"UorAtlas")
                        && !text.contains("\"imports\":[\"Init\",\"UorAtlas")
                }),
                "the native cores never import the migration oracle"
            );
        }
        other => panic!("no verification case is wired for {other}"),
    }
}

/// The platform-independent half of each Lean-backed case, run on hosts
/// without the pinned toolchain (§8.3): the format and option contracts
/// that need no Lean process.
fn run_platform_independent(id: &str) {
    match id {
        "VR-01" => {
            let project = P::example();
            for forbidden in [
                ["verify", "--skip-audit"],
                ["verify", "--no-replay"],
                ["verify", "--output"],
            ] {
                let (exit, _, _) = project.cli(&forbidden);
                assert_eq!(exit, 2, "verify rejects {forbidden:?}");
            }
        }
        "VR-04" => {
            let (probe, audit) = lexlean::verify::reserved_module_names(
                lexlean::artifact::content_id::Sha256Digest::of(b"x"),
            );
            assert!(probe.starts_with("LexLeanProbe.P") && audit.starts_with("LexLeanAudit.A"));
            assert_ne!(probe, audit);
        }
        "VR-13" | "VR-14" => {
            for name in ["attestation", "build-manifest", "source-map", "coverage"] {
                let schema = support::schema(name);
                assert_eq!(
                    schema["$schema"].as_str(),
                    Some("https://json-schema.org/draft/2020-12/schema")
                );
            }
        }
        _ => {
            // Every other Lean-backed case has no assertion that is
            // meaningful without the toolchain; the host gate reported that.
        }
    }
}
