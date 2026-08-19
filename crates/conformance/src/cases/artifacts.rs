//! The `artifacts` suite: AR-01..AR-14.

use lexlean::artifact::canonical_json::Json;
use lexlean::artifact::content_id::{FramedHasher, Sha256Digest};
use sha2::Digest;

use crate::support::{self, P};

pub(crate) fn run(id: &str) {
    match id {
        // §20.1, §20.6: canonical diagnostics with stable order.
        "AR-01" => {
            let project = P::example();
            project.edit(
                "src/Main.lex.tex",
                "For every natural number",
                "For banana every kumquat natural number",
            );
            let (exit, stdout, stderr) = project.cli(&["--diagnostic-format", "json", "check"]);
            assert_ne!(exit, 0);
            assert!(stderr.is_empty(), "JSON mode leaves stderr empty: {stderr}");
            let value: serde_json::Value =
                serde_json::from_str(&stdout).expect("one canonical JSON object");
            let diagnostics = value["diagnostics"].as_array().expect("diagnostics");
            assert!(!diagnostics.is_empty());
            let model =
                repo_model::Model::load(&support::repo_root().join("model").into_std_path_buf())
                    .expect("model");
            let mut offsets = Vec::new();
            for diagnostic in diagnostics {
                let code = diagnostic["code"].as_str().expect("a code");
                assert!(
                    model.errors.get(code).is_some(),
                    "`{code}` is a registered code"
                );
                if let Some(start) = diagnostic["primary"]["byte_start"].as_u64() {
                    offsets.push(start);
                }
            }
            let mut sorted = offsets.clone();
            sorted.sort_unstable();
            assert_eq!(offsets, sorted, "diagnostics sort by position");
            // A failed check established no ID: absent IDs are omitted,
            // never null (§20.6).
            for absent in ["source_id", "semantic_id", "build_id", "attestation_id"] {
                assert!(
                    value.get(absent).is_none(),
                    "`{absent}` is omitted when unknown: {value}"
                );
            }

            // A successful check reports the source and semantic IDs; a
            // build adds the build ID (§20.6).
            let project = P::example();
            let checked = support::checked_project(&project);
            let (exit, stdout, _) = project.cli(&["--diagnostic-format", "json", "check"]);
            assert_eq!(exit, 0);
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            assert_eq!(
                value["source_id"].as_str(),
                Some(checked.source_id.to_hex().as_str()),
                "check reports the source ID"
            );
            assert_eq!(
                value["semantic_id"].as_str(),
                Some(checked.semantic_id.to_hex().as_str()),
                "check reports the semantic ID"
            );
            assert!(value.get("build_id").is_none(), "check has no build ID");
            let (exit, stdout, _) = project.cli(&["--diagnostic-format", "json", "build"]);
            assert_eq!(exit, 0);
            let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
            let build_id =
                lexlean::artifact::content_id::build_id(checked.source_id, checked.semantic_id);
            assert_eq!(
                value["build_id"].as_str(),
                Some(build_id.to_hex().as_str()),
                "build reports the build ID"
            );
            assert!(
                value.get("attestation_id").is_none(),
                "build has no attestation ID"
            );
        }
        // §20.3: complete source-map records.
        "AR-02" => {
            let build = support::rendered(&P::example());
            let map = &build.modules[0].map;
            assert!(!map.artifacts.is_empty(), "artifact records exist");
            assert!(!map.nodes.is_empty(), "node records exist");
            assert!(!map.mappings.is_empty(), "mapping records exist");
            assert!(!map.sources.is_empty(), "source records exist");
            let node_ids: std::collections::BTreeSet<usize> =
                map.nodes.iter().map(|node| node.id).collect();
            let artifact_ids: std::collections::BTreeSet<usize> =
                map.artifacts.iter().map(|artifact| artifact.id).collect();
            for mapping in &map.mappings {
                assert!(
                    node_ids.contains(&mapping.node),
                    "every mapping names a real node"
                );
                assert!(
                    artifact_ids.contains(&mapping.artifact),
                    "every mapping names a real artifact"
                );
                assert!(mapping.gen_start <= mapping.gen_end, "sane ranges");
                if let Some((start, end)) = mapping.src_range {
                    assert!(
                        (start, end) != (0, 0),
                        "no fabricated (0,0) source span: {mapping:?}"
                    );
                }
            }
            // Roles are clause-granular (§20.3): the lifted binder maps
            // under `binder` to its own introduction, proof tokens under
            // `proof` to their step, LaTeX controls under `renderer`, and
            // the preamble under `synthetic`.
            use lexlean::artifact::source_map::MapRole;
            let module = &build.modules[0];
            let source = support::checked_project(&P::example());
            let normalized = &source.modules["Main"].normalized;
            let binder_at = module
                .lean_text
                .find("(llv0 : Nat)")
                .expect("the parameter");
            let binder = map.remap(0, binder_at + 1).expect("mapped");
            assert_eq!(binder.role, MapRole::Binder, "parameters map as binders");
            let (start, end) = binder.src_range.expect("a source range");
            assert_eq!(
                &normalized[start..end],
                "n",
                "the binder maps to its own introduction"
            );
            let rfl_at = module.lean_text.find("rfl").expect("rfl");
            let proof = map.remap(0, rfl_at).expect("mapped");
            assert_eq!(proof.role, MapRole::Proof);
            let (start, end) = proof.src_range.expect("a source range");
            assert_eq!(
                &normalized[start..end],
                "Close the goal by reflexivity.",
                "a proof token maps to exactly its step"
            );
            let control_at = module.tex_text.find("\\begin{proof}").expect("proof env");
            let control = map.remap(1, control_at).expect("mapped");
            assert_eq!(
                control.role,
                MapRole::Renderer,
                "LaTeX controls map as renderer"
            );
            let preamble = map.remap(1, 0).expect("mapped");
            assert_eq!(
                preamble.role,
                MapRole::Synthetic,
                "the preamble is synthetic"
            );
            let module_at = module.lean_text.find("module").expect("module keyword");
            assert_eq!(
                map.remap(0, module_at).expect("mapped").role,
                MapRole::Synthetic
            );
        }
        // §20.4: the smallest-enclosing remap algorithm.
        "AR-03" => {
            let build = support::rendered(&P::example());
            let module = &build.modules[0];
            let map = &module.map;
            let lean_artifact = map
                .artifacts
                .iter()
                .find(|artifact| artifact.path.ends_with(".lean"))
                .expect("the lean artifact")
                .id;
            let rfl_at = module.lean_text.find("rfl").expect("rfl");
            let mapping = map
                .remap(lean_artifact, rfl_at)
                .expect("rfl remaps to source");
            // The winner is a smallest enclosing mapping (§20.4 tie order).
            let enclosing: Vec<_> = map
                .mappings
                .iter()
                .filter(|candidate| {
                    candidate.artifact == lean_artifact
                        && candidate.gen_start <= rfl_at
                        && rfl_at < candidate.gen_end
                })
                .collect();
            let smallest = enclosing
                .iter()
                .map(|candidate| candidate.gen_end - candidate.gen_start)
                .min()
                .expect("a candidate");
            assert_eq!(
                mapping.gen_end - mapping.gen_start,
                smallest,
                "remap picks a smallest enclosing mapping"
            );
            assert!(
                mapping.role != lexlean::artifact::source_map::MapRole::Synthetic,
                "a proof token maps to a real proof origin"
            );
            // Lean columns count Unicode scalar values (§20.1); the byte
            // conversion is per line.
            use lexlean::verify::{lean_position_to_byte, parse_lean_messages};
            let text = "ab\n  refine ⟨x, ?_⟩\nend\n";
            assert_eq!(lean_position_to_byte(text, 1, 1), Some(1));
            assert_eq!(lean_position_to_byte(text, 2, 9), Some(3 + 9));
            assert_eq!(
                lean_position_to_byte(text, 2, 10),
                Some(3 + 9 + '⟨'.len_utf8()),
                "the column after a multi-byte scalar advances by its byte length"
            );
            assert_eq!(
                lean_position_to_byte(text, 3, 0),
                Some(3 + "  refine ⟨x, ?_⟩".len() + 1)
            );
            assert_eq!(lean_position_to_byte(text, 9, 0), None);
            // Every located message is parsed, continuation lines join.
            let messages = parse_lean_messages(
                "$S/A.lean:3:2: error: first\n  detail\n$S/A.lean:5:4: warning: second\nnoise\n$S/A.lean:7:0: info: third\n",
            );
            assert_eq!(messages.len(), 3);
            assert_eq!(messages[0].line, 3);
            assert_eq!(messages[0].column, 2);
            assert_eq!(messages[0].severity, "error");
            assert_eq!(messages[0].message, "first\n  detail");
            assert_eq!(messages[1].severity, "warning");
            assert_eq!(messages[1].message, "second\nnoise");
            assert_eq!(messages[2].line, 7);
            // The remapped verification failure of the shared broken proof
            // carries a real source span and the generated location note.
            // Producing the failure means running Lean (§8.3); every
            // assertion above is a diagnostic-rendering property and runs on
            // every supported host.
            if !support::lean_backed("AR-03") {
                return;
            }
            let (project, error) = support::broken_proof();
            let diagnostic = error
                .diagnostics
                .iter()
                .find(|diagnostic| diagnostic.code.as_str() == "LLV7002")
                .expect("the Lean failure");
            let span = diagnostic.primary.as_ref().expect("a primary source span");
            let source = project.read("src/Main.lex.tex");
            assert_eq!(
                &source[span.byte_start..span.byte_end],
                "Close the goal by reflexivity.",
                "the failing rfl maps to its proof step"
            );
            assert!(
                diagnostic
                    .notes
                    .iter()
                    .any(|note| note.message.starts_with("generated location: ")),
                "the generated location is a note: {diagnostic:?}"
            );
        }
        // §20.5: complete coverage files with no gap or overlap.
        "AR-04" => {
            let project = P::example();
            let build = project.build_ok();
            let build_id = build.build_id.expect("built");
            let files = support::file_set(&project.build_dir(&build_id));
            assert!(
                files.contains("coverage/LexLeanExample/Main.coverage.json"),
                "the coverage artifact is published: {files:?}"
            );
            let rendered = support::rendered(&project);
            let module = &rendered.modules[0];
            // Output rows partition (LN-10/TX-06 check per-byte; here the
            // row discipline itself).
            for rows in [&module.coverage.lean, &module.coverage.latex] {
                for pair in rows.windows(2) {
                    assert!(
                        pair[0].byte_end <= pair[1].byte_start,
                        "rows are sorted and non-overlapping"
                    );
                }
            }
            assert!(!module.coverage.source.is_empty(), "source rows recorded");
            // The mechanical closure check (§20.5) accepts the real rows and
            // rejects a synthetic gap, overlap, and out-of-range row.
            use lexlean::backend::check_output_closure;
            use lexlean::source::coverage::{Origin, OutputRow};
            check_output_closure(&module.lean_text, &module.coverage.lean)
                .expect("lean rows close");
            check_output_closure(&module.tex_text, &module.coverage.latex).expect("tex rows close");
            let row = |start: usize, end: usize| OutputRow {
                byte_start: start,
                byte_end: end,
                kind: "word".to_owned(),
                origin: Origin::Numeral,
            };
            assert_eq!(
                check_output_closure("ab cd", &[row(0, 2)]),
                Err("coverage gap at bytes 3..5".to_owned())
            );
            assert_eq!(
                check_output_closure("ab cd", &[row(0, 2), row(1, 5)]),
                Err("coverage overlap at bytes 1..2".to_owned())
            );
            assert_eq!(
                check_output_closure("ab", &[row(0, 3)]),
                Err("coverage row 0..3 lies outside the 2-byte output".to_owned())
            );
            assert_eq!(
                check_output_closure("ab  cd\n", &[row(0, 2), row(4, 6)]),
                Ok(())
            );
            let mut broken = module.coverage.lean.clone();
            broken.pop();
            assert!(check_output_closure(&module.lean_text, &broken).is_err());
        }
        // §21.1: the exact frame function.
        "AR-05" => {
            let mut framed = FramedHasher::new("t");
            framed.frame("a", b"xy");
            framed.frame("b", b"");
            let mut manual = sha2::Sha256::new();
            manual.update(b"t\0");
            manual.update(1u32.to_be_bytes());
            manual.update(b"a");
            manual.update(2u64.to_be_bytes());
            manual.update(b"xy");
            manual.update(1u32.to_be_bytes());
            manual.update(b"b");
            manual.update(0u64.to_be_bytes());
            let digest: [u8; 32] = manual.finalize().into();
            assert_eq!(framed.finish(), Sha256Digest(digest), "§21.1 byte layout");
        }
        // §21.2: the semantics ID is sensitive to every normative input.
        "AR-06" => {
            // Recompute independently from the repository files (§21.2):
            // every regular file under language/, schemas/, and the two
            // golden fixture directories, in bytewise path order.
            let root = support::repo_root();
            let mut disk: Vec<(String, Vec<u8>)> = Vec::new();
            for dir in [
                "language",
                "schemas",
                "tests/golden/axiom-parser",
                "tests/golden/canonical-json",
            ] {
                for entry in walkdir::WalkDir::new(root.join(dir).as_std_path())
                    .into_iter()
                    .flatten()
                {
                    if entry.file_type().is_file() {
                        let relative = entry
                            .path()
                            .strip_prefix(root.as_std_path())
                            .expect("under root")
                            .to_string_lossy()
                            .replace('\\', "/");
                        disk.push((relative, std::fs::read(entry.path()).expect("read")));
                    }
                }
            }
            disk.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
            let disk_refs: Vec<(&str, &[u8])> = disk
                .iter()
                .map(|(path, bytes)| (path.as_str(), bytes.as_slice()))
                .collect();
            assert_eq!(
                lexlean::artifact::content_id::tree_digest(&disk_refs),
                lexlean::compiler_semantics_id(),
                "the on-disk normative set reproduces the embedded ID"
            );
            let files: Vec<(&str, &[u8])> = lexlean::embedded::FILES.to_vec();
            assert_eq!(
                files, disk_refs,
                "the embedded set is exactly the on-disk set"
            );
            let mut mutated = files.clone();
            let flipped = b"tampered".as_slice();
            mutated[0].1 = flipped;
            assert_ne!(
                lexlean::artifact::content_id::tree_digest(&mutated),
                lexlean::compiler_semantics_id(),
                "one changed input changes the ID"
            );
        }
        // §21.3: location-independent, input-exact source IDs.
        "AR-07" => {
            let first = P::example();
            let second = P::example();
            assert_ne!(first.root, second.root, "distinct absolute locations");
            assert_eq!(
                support::checked_project(&first).source_id,
                support::checked_project(&second).source_id,
                "the source ID excludes the checkout location"
            );
            second.edit("src/Main.lex.tex", "{add-zero}", "{add-zeros}");
            assert_ne!(
                support::checked_project(&first).source_id,
                support::checked_project(&second).source_id,
                "normalized source bytes are included"
            );
        }
        // §21.4: platform/location-independent semantic IDs.
        "AR-08" => {
            let first = P::example();
            let second = P::example();
            assert_eq!(
                support::checked_project(&first).semantic_id,
                support::checked_project(&second).semantic_id
            );
            assert_ne!(
                support::checked_project(&first).semantic_id,
                support::checked_project(&support::defs_project()).semantic_id,
                "linked IR and closure flow into the ID"
            );
        }
        // §21.5: the fixed content-addressed layout, exactly.
        "AR-09" => {
            let project = P::example();
            let build = project.build_ok();
            let build_id = build.build_id.expect("built");
            let files = support::file_set(&project.build_dir(&build_id));
            let expected: std::collections::BTreeSet<String> = [
                "manifest.json",
                "modules/LexLeanExample/Main.lean",
                "modules/LexLeanExample/Main.tex",
                "maps/LexLeanExample/Main.map.json",
                "coverage/LexLeanExample/Main.coverage.json",
                "lexicons/Main.closure.json",
            ]
            .into_iter()
            .map(str::to_owned)
            .collect();
            assert_eq!(files, expected, "§21.5: exactly the fixed artifact set");
        }
        // §21.6: the manifest enumerates every input and output exactly.
        "AR-10" => {
            let project = P::example();
            let build = project.build_ok();
            let build_id = build.build_id.expect("built");
            let build_dir = project.build_dir(&build_id);
            let manifest: serde_json::Value = serde_json::from_slice(
                &std::fs::read(build_dir.join("manifest.json").as_std_path()).expect("read"),
            )
            .expect("parses");
            for key in [
                "spec",
                "compiler",
                "language",
                "project",
                "source_id",
                "semantic_id",
                "build_id",
                "lean_toolchain",
                "selection",
                "modules",
                "inputs",
                "outputs",
            ] {
                assert!(manifest.get(key).is_some(), "§21.6 field `{key}`");
            }
            let inputs = manifest["inputs"].as_array().expect("inputs");
            for required in ["src/Main.lex.tex", "lexlean.toml", "lexlean.lock"] {
                assert!(
                    inputs
                        .iter()
                        .any(|row| row["path"].as_str() == Some(required)),
                    "inputs enumerate {required}: {inputs:?}"
                );
            }
            let lexicon_rows: Vec<&str> = inputs
                .iter()
                .filter(|row| row["kind"].as_str() == Some("lexicon"))
                .map(|row| row["path"].as_str().expect("path"))
                .collect();
            // Every builtin lexicon input names the embedded source, and there
            // is exactly one row per builtin package the project locks. The
            // count is bootstrap data, not a property of §21.6: making
            // `lexlean.uor.atlas` unconditional locks its whole import closure
            // into every project, so a literal here would encode the size of
            // that closure and go stale the next time it changes.
            let locked_builtins =
                std::fs::read_to_string(project.root.join("lexlean.lock").as_std_path())
                    .expect("the project is locked")
                    .lines()
                    .filter(|line| line.trim() == "kind = \"builtin\"")
                    .count();
            assert!(
                locked_builtins > 0 && lexicon_rows.len() == locked_builtins,
                "one embedded lexicon input per locked builtin package ({locked_builtins}): {inputs:?}"
            );
            assert!(
                lexicon_rows.iter().all(|path| *path == "embedded"),
                "builtin lexicon input rows name the embedded source: {inputs:?}"
            );
            let defs = support::defs_project();
            let defs_build = support::rendered(&defs);
            let defs_manifest: serde_json::Value =
                serde_json::from_slice(&defs_build.manifest_bytes).expect("parses");
            let path_rows: Vec<&str> = defs_manifest["inputs"]
                .as_array()
                .expect("inputs")
                .iter()
                .filter(|row| row["kind"].as_str() == Some("lexicon"))
                .map(|row| row["path"].as_str().expect("path"))
                .collect();
            assert!(
                path_rows.contains(&"lexicons/test-defs"),
                "a path package input row carries its project-relative path: {path_rows:?}"
            );
            for row in manifest["outputs"].as_array().expect("outputs") {
                let path = row["path"].as_str().expect("path");
                let bytes =
                    std::fs::read(build_dir.join(path).as_std_path()).expect("output exists");
                assert_eq!(
                    row["byte_length"].as_u64(),
                    Some(bytes.len() as u64),
                    "{path}: exact length"
                );
                assert_eq!(
                    row["sha256"].as_str(),
                    Some(Sha256Digest::of(&bytes).to_hex().as_str()),
                    "{path}: exact hash"
                );
            }
        }
        // §21.7: the restricted canonical JSON and the newline distinction.
        "AR-11" => {
            assert!(Json::parse(b"1.5").is_err(), "floats are rejected");
            assert!(Json::parse(b"null").is_err(), "null is rejected");
            assert!(
                Json::parse(b"{\"a\":1,\"a\":2}").is_err(),
                "duplicate keys are rejected"
            );
            assert!(
                Json::parse(b"{\"a\":{\"b\":1,\"b\":2}}").is_err(),
                "nested duplicate keys are rejected"
            );
            assert!(
                Json::parse(b"{\"a\":[{\"b\":1},{\"b\":2}]}").is_ok(),
                "equal keys in distinct objects are not duplicates"
            );
            assert!(
                Json::parse(b"{\"a\":\"x\\\"a\",\"b\":1}").is_ok(),
                "an escaped quote inside a value is not a key"
            );
            let object = Json::object(vec![
                ("zebra", Json::from_usize(1)),
                ("alpha", Json::from_usize(2)),
            ]);
            let canonical = object.to_canonical_string();
            assert_eq!(
                canonical, "{\"alpha\":2,\"zebra\":1}",
                "sorted keys, no spaces"
            );
            let file_bytes = object.to_file_bytes();
            assert_eq!(
                file_bytes, b"{\"alpha\":2,\"zebra\":1}\n",
                "file form adds exactly one final LF; the hash form has none"
            );
            // The committed canonical-JSON fixture table (§21.2 digests it):
            // one `input<TAB>canonical` row per line; every row must parse
            // and re-serialize to exactly its canonical column, and the
            // canonical column must be a fixed point.
            let table = std::fs::read_to_string(
                support::repo_root()
                    .join("tests/golden/canonical-json/values.txt")
                    .as_std_path(),
            )
            .expect("the canonical-json fixture table");
            let mut rows = 0usize;
            for (number, line) in table.lines().enumerate() {
                if line.is_empty() {
                    continue;
                }
                let (input, expected) = line.split_once('\t').unwrap_or_else(|| {
                    panic!("values.txt line {}: input<TAB>canonical", number + 1)
                });
                let parsed = Json::parse(input.as_bytes())
                    .unwrap_or_else(|error| panic!("values.txt line {}: {error}", number + 1));
                assert_eq!(
                    parsed.to_canonical_string(),
                    expected,
                    "values.txt line {}: canonical form",
                    number + 1
                );
                let reparsed = Json::parse(expected.as_bytes()).expect("canonical parses");
                assert_eq!(
                    reparsed.to_canonical_string(),
                    expected,
                    "values.txt line {}: canonical form is a fixed point",
                    number + 1
                );
                rows += 1;
            }
            assert!(rows >= 6, "the fixture table is populated ({rows} rows)");
        }
        // §21.8: atomic, content-addressed, never silently overwritten.
        "AR-12" => {
            let project = P::example();
            let build = project.build_ok();
            let build_id = build.build_id.expect("built");
            let build_dir = project.build_dir(&build_id);

            // Concurrent rebuilds converge on one valid publication.
            std::thread::scope(|scope| {
                let handles: Vec<_> = (0..2)
                    .map(|_| {
                        scope.spawn(|| {
                            project
                                .engine()
                                .build(lexlean::BuildRequest {
                                    selection: lexlean::Selection::Entrypoints,
                                })
                                .map(|result| result.build_id)
                        })
                    })
                    .collect();
                for handle in handles {
                    let result = handle.join().expect("no panic");
                    assert!(result.is_ok(), "concurrent builds succeed: {result:?}");
                }
            });
            assert!(build_dir.as_std_path().is_dir());

            // A corrupted published byte is detected, not silently replaced.
            let lean_path = build_dir.join("modules/LexLeanExample/Main.lean");
            let mut bytes = std::fs::read(lean_path.as_std_path()).expect("read");
            bytes[0] ^= 0x01;
            std::fs::write(lean_path.as_std_path(), &bytes).expect("corrupt");
            let error = project
                .engine()
                .build(lexlean::BuildRequest {
                    selection: lexlean::Selection::Entrypoints,
                })
                .err()
                .expect("unexplained bytes at the build path are an error");
            support::expect_code(&error, "LLB6003");

            // An unexplained extra file in the published set is detected.
            let fresh = P::example();
            let fresh_build = fresh.build_ok();
            let fresh_dir = fresh.build_dir(&fresh_build.build_id.expect("built"));
            std::fs::write(fresh_dir.join("extra.txt").as_std_path(), b"x").expect("plant");
            let error = fresh
                .engine()
                .build(lexlean::BuildRequest {
                    selection: lexlean::Selection::Entrypoints,
                })
                .err()
                .expect("an extra file refuses reuse");
            support::expect_code(&error, "LLB6003");
            assert!(
                error.to_string().contains("extra.txt"),
                "the extra file is named: {error}"
            );
            // §23.7: both branches of the reuse check print the build
            // directory project-relative, so the message reads the same on
            // every host and stays byte-comparable.
            let rendered = error.to_string();
            assert!(
                rendered.contains(&format!(
                    ".lexlean/build/{}",
                    fresh_build.build_id.expect("built").to_hex()
                )),
                "the build directory is project-relative: {rendered}"
            );
            assert!(
                !rendered.contains(fresh.root.as_str()),
                "no absolute path leaks into the diagnostic: {rendered}"
            );

            // No staging residue anywhere.
            for entry in walkdir::WalkDir::new(project.root.join(".lexlean").as_std_path())
                .into_iter()
                .flatten()
            {
                let name = entry.file_name().to_string_lossy().into_owned();
                assert!(
                    !name.contains(".staging"),
                    "staging is removed after publication or failure: {name}"
                );
            }
        }
        // §28.4: byte-identical builds in distinct absolute directories.
        "AR-13" => {
            let first = support::rendered(&P::example());
            let second = support::rendered(&P::example());
            assert_eq!(first.build_id, second.build_id);
            assert_eq!(
                first.files.len(),
                second.files.len(),
                "identical artifact sets"
            );
            for ((path_a, bytes_a), (path_b, bytes_b)) in first.files.iter().zip(&second.files) {
                assert_eq!(path_a, path_b);
                assert_eq!(bytes_a, bytes_b, "{path_a} is byte-identical");
            }
        }
        // §22.8, AR-14: platform-bound evidence is separated.
        "AR-14" => {
            let Some(fixture) = support::example_backed("AR-14") else {
                return;
            };
            let verified_files = support::file_set(&fixture.outcome.root);
            assert!(
                verified_files.iter().any(|file| file.ends_with(".olean")),
                "oleans live in the verified set"
            );
            assert!(verified_files.contains("attestation.json"));
            assert!(
                verified_files
                    .iter()
                    .any(|file| file.starts_with("process/lean/")),
                "process records live in the verified set"
            );

            let project = &fixture.project;
            let build_dir = project.build_dir(&fixture.outcome.build_id);
            let build_files = support::file_set(&build_dir);
            for file in &build_files {
                assert!(
                    !file.ends_with(".olean")
                        && !file.contains("process/")
                        && file != "attestation.json"
                        && !file.ends_with(".pdf"),
                    "platform-bound evidence never enters the build set: {file}"
                );
            }
        }
        other => panic!("no artifacts case is wired for {other}"),
    }
}
