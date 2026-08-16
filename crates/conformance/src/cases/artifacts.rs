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
            }
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
            let files: Vec<(&str, &[u8])> = lexlean::embedded::FILES.to_vec();
            assert_eq!(
                lexlean::artifact::content_id::tree_digest(&files),
                lexlean::compiler_semantics_id(),
                "the embedded set reproduces the ID"
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
            let fixture = support::verified();
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
