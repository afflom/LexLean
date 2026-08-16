//! The `latex-pdf` suite: TX-01..TX-12.

use lexlean::artifact::content_id::Sha256Digest;
use lexlean::config::PdfProvider;

use crate::support::{self, P};

/// The §29.4 preamble, byte for byte.
const PREAMBLE: &str = "\\documentclass[11pt]{article}\n\\usepackage[T1]{fontenc}\n\\usepackage{amsmath}\n\\usepackage{amssymb}\n\\usepackage{amsthm}\n\\usepackage[hidelinks]{hyperref}\n\\newtheorem{theorem}{Theorem}[section]\n\\newtheorem{lemma}[theorem]{Lemma}\n\\newtheorem{corollary}[theorem]{Corollary}\n\\theoremstyle{definition}\n\\newtheorem{definition}[theorem]{Definition}\n\\begin{document}\n";

/// Install the fake PDF provider script and return its configuration.
fn fake_provider(project: &P, exit_code: i32) -> PdfProvider {
    let script = format!(
        "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then exit 0; fi\nname=$(basename \"$3\" .tex)\n{{ printf '%%PDF-fake\\n'; pwd; ls -A .; }} > \"$2/$name.pdf\"\nexit {exit_code}\n"
    );
    project.write("tools/fakepdf", &script);
    let script_path = project.root.join("tools/fakepdf");
    let mut permissions = std::fs::metadata(script_path.as_std_path())
        .expect("stat")
        .permissions();
    std::os::unix::fs::PermissionsExt::set_mode(&mut permissions, 0o755);
    std::fs::set_permissions(script_path.as_std_path(), permissions).expect("chmod");
    PdfProvider {
        program: "tools/fakepdf".to_owned(),
        program_sha256: Sha256Digest::of(script.as_bytes()),
        version_argv: vec!["--version".to_owned()],
        version_stdout_sha256: Sha256Digest::of(b"\n"),
        compile_argv: vec![
            "--outdir".to_owned(),
            "{out_dir}".to_owned(),
            "{input}".to_owned(),
        ],
        output: "{stem}.pdf".to_owned(),
        resources: Vec::new(),
    }
}

fn run_fake_provider(
    project: &P,
    provider: &PdfProvider,
) -> Result<lexlean::backend::pdf::PdfResult, lexlean::diagnostic::Diagnostic> {
    let inner = lexlean::project::Project::load(&project.root.join("lexlean.toml")).expect("load");
    let build = support::rendered(project);
    let staging = project.root.join(".lexlean");
    std::fs::create_dir_all(staging.as_std_path()).expect("staging parent");
    lexlean::backend::pdf::run_provider(
        &inner,
        provider,
        build.modules[0].tex_text.as_bytes(),
        &build.modules[0].lean_module,
        &staging,
    )
}

pub(crate) fn run(id: &str) {
    match id {
        // §19.1: rendered solely from linked IR, deterministically.
        "TX-01" => {
            let project = P::example();
            let first = support::tex_text(&support::rendered(&project), "Main");
            let second = support::tex_text(&support::rendered(&project), "Main");
            assert_eq!(first, second, "rendering is a pure function of linked IR");
            // The canonical proof prose is regenerated, not copied: the
            // source sentence spelling does not appear.
            assert!(
                !first.contains("Close the goal by reflexivity"),
                "source proof prose is not copied: {first}"
            );
            assert!(
                first.contains("The goal follows by reflexivity."),
                "the canonical §29.4 proof rendering is generated: {first}"
            );
        }
        // §19.2: the exact preamble, no host or timestamp metadata.
        "TX-02" => {
            let tex = support::tex_text(&support::rendered(&P::example()), "Main");
            assert!(
                tex.starts_with(PREAMBLE),
                "the §29.4 preamble opens every module: {tex}"
            );
            for forbidden in ["\\today", "\\date", "hostname"] {
                assert!(!tex.contains(forbidden), "no host or time metadata: {tex}");
            }
        }
        // §19.4: canonical proposition renderings only.
        "TX-03" => {
            let tex = support::tex_text(&support::rendered(&P::example()), "Main");
            assert!(
                tex.contains("For every natural number \\(n\\), \\(n + 0 = n\\)."),
                "the canonical §29.4 statement rendering: {tex}"
            );
        }
        // §19.5: proof prose from proof IR with fixed core forms.
        "TX-04" => {
            let tex = support::tex_text(&support::rendered(&P::example()), "Main");
            assert!(
                tex.contains("\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}"),
                "the canonical proof block: {tex}"
            );
        }
        // §19.3: exact document structure, numbering, and labels.
        "TX-05" => {
            let tex = support::tex_text(&support::rendered(&P::example()), "Main");
            for required in [
                "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}",
                "\\begin{theorem}\n\\label{ll:main:add-zero}",
                "\\newtheorem{theorem}{Theorem}[section]",
                "\\end{document}",
            ] {
                assert!(tex.contains(required), "§29.4 requires {required:?}: {tex}");
            }
        }
        // §19.6: complete output lexical coverage.
        "TX-06" => {
            let build = support::rendered(&P::example());
            let module = &build.modules[0];
            let bytes = module.tex_text.as_bytes();
            for (index, byte) in bytes.iter().enumerate() {
                if byte.is_ascii_whitespace() {
                    continue;
                }
                let covering = module
                    .coverage
                    .latex
                    .iter()
                    .filter(|row| row.byte_start <= index && index < row.byte_end)
                    .count();
                assert_eq!(
                    covering,
                    1,
                    "tex byte {index} ({:?}) is covered exactly once, found {covering}",
                    module.tex_text[index..].chars().next()
                );
            }
        }
        // §13.10: no raw TeX injection from non-core lexicons.
        "TX-07" => {
            let project = P::example();
            project.add_package(
                "lexicons/test-evil",
                "test.evil",
                &["lexlean.core@1.0.0"],
                &[(
                    "evil.toml",
                    r#"spec = "lexlean/entry/1"
id = "evil"
category = "term-constant"
signature = "(const lexlean.std.nat::nat)"
surface_arity = 0
frame = "atom"

[denotation]
kind = "lean"
module = "Init"
name = "Nat.zero"

[[form]]
id = "evil"
channel = "math"
surface = "evil"
canonical_source = true
features = []

[render]
math = "(token write18)"
"#,
                )],
            );
            let error = project
                .engine()
                .lock(lexlean::LockRequest {
                    check_only: false,
                    allow_network: false,
                })
                .err()
                .expect("an unregistered output token is rejected");
            support::expect_code(&error, "LLR3004");
        }
        // §19.1: deterministic LF-terminated bytes.
        "TX-08" => {
            let tex = support::tex_text(&support::rendered(&P::example()), "Main");
            assert!(tex.ends_with('\n'), "one final LF");
            assert!(!tex.contains('\r'), "LF only");
            assert_eq!(
                tex,
                support::tex_text(&support::rendered(&P::example()), "Main"),
                "deterministic bytes"
            );
        }
        // §19.7: hash-checked, shell-free, isolated execution.
        "TX-09" => {
            let project = P::example();
            let mut provider = fake_provider(&project, 0);

            // A wrong executable hash refuses to run.
            let correct = provider.program_sha256;
            provider.program_sha256 = Sha256Digest::of(b"not the program");
            let error = run_fake_provider(&project, &provider).expect_err("hash mismatch");
            assert_eq!(
                error.code.as_str(),
                "LLS8004",
                "SE-08: refused before execution"
            );

            // The honest hash runs in an isolated directory seeing only the
            // canonical TeX.
            provider.program_sha256 = correct;
            let result = run_fake_provider(&project, &provider).expect("the provider runs");
            let recorded = String::from_utf8_lossy(&result.pdf_bytes).into_owned();
            assert!(recorded.starts_with("%PDF-"), "the output is a PDF stream");
            let workdir = recorded.lines().nth(1).expect("the recorded pwd");
            assert_ne!(workdir, project.root.as_str(), "not the project root");
            assert!(
                workdir.contains("/.lexlean/") && workdir.ends_with("/work"),
                "an isolated staging working directory: {workdir}"
            );
            let listing: Vec<&str> = recorded
                .lines()
                .skip(2)
                .filter(|line| !line.is_empty())
                .collect();
            assert_eq!(
                listing,
                vec!["LexLeanExample.Main.tex"],
                "the provider sees exactly the canonical TeX: {recorded}"
            );
        }
        // §19.8: the recipe ID and the PDF hash are independent records.
        "TX-10" => {
            let project = P::example();
            let provider = fake_provider(&project, 0);
            let result = run_fake_provider(&project, &provider).expect("runs");

            // Recompute the recipe per the §19.8 layout.
            use sha2::Digest;
            let build = support::rendered(&project);
            let mut hasher = sha2::Sha256::new();
            hasher.update(b"lexlean-pdf-recipe-v1\0");
            let frame = |hasher: &mut sha2::Sha256, label: &str, bytes: &[u8]| {
                hasher.update(u32::try_from(label.len()).expect("short").to_be_bytes());
                hasher.update(label.as_bytes());
                hasher.update((bytes.len() as u64).to_be_bytes());
                hasher.update(bytes);
            };
            let tex_hash = Sha256Digest::of(build.modules[0].tex_text.as_bytes());
            frame(&mut hasher, "tex", &tex_hash.0);
            frame(&mut hasher, "program", &provider.program_sha256.0);
            frame(
                &mut hasher,
                "version-output",
                &provider.version_stdout_sha256.0,
            );
            let argv_json = lexlean::artifact::canonical_json::Json::Arr(
                provider
                    .compile_argv
                    .iter()
                    .map(|argument| lexlean::artifact::canonical_json::Json::Str(argument.clone()))
                    .collect(),
            )
            .to_canonical_string();
            frame(&mut hasher, "argv", argv_json.as_bytes());
            frame(&mut hasher, "resources", b"[]");
            let manual: [u8; 32] = hasher.finalize().into();
            assert_eq!(
                Sha256Digest(manual),
                result.recipe_id,
                "§19.8: the recipe ID uses exactly the specified frames"
            );
            assert_eq!(
                result.pdf_sha256,
                Sha256Digest::of(&result.pdf_bytes),
                "the actual PDF hash is recorded separately"
            );
            assert_ne!(
                result.recipe_id.to_hex(),
                result.pdf_sha256.to_hex(),
                "recipe and content are independent records"
            );
        }
        // §19.7, §19.8: PDF never carries mathematical authority.
        "TX-11" => {
            let project = P::example();
            let provider = fake_provider(&project, 1);
            let error = run_fake_provider(&project, &provider)
                .expect_err("a failing provider is a PDF failure");
            assert_eq!(
                error.code.as_str(),
                "LLB6004",
                "the failure is a PDF-protocol code, not a verification claim"
            );

            // Configuring a provider does not perturb the semantic ID.
            let without = support::checked_project(&P::example()).semantic_id;
            let with_pdf = P::example();
            let _ = fake_provider(&with_pdf, 0);
            let program_hash = Sha256Digest::of(with_pdf.read("tools/fakepdf").as_bytes());
            with_pdf.edit(
                "lexlean.toml",
                "\n[limits]",
                &format!(
                    "\n[pdf]\nmode = \"external\"\nprogram = \"tools/fakepdf\"\nprogram_sha256 = \"{}\"\nversion_argv = [\"--version\"]\nversion_stdout_sha256 = \"{}\"\ncompile_argv = [\"--outdir\", \"{{out_dir}}\", \"{{input}}\"]\noutput = \"{{stem}}.pdf\"\nresources = []\n\n[limits]",
                    program_hash.to_hex(),
                    Sha256Digest::of(b"\n").to_hex()
                ),
            );
            with_pdf.relock();
            assert_eq!(
                support::checked_project(&with_pdf).semantic_id,
                without,
                "§19.8: PDF configuration does not affect the semantic ID"
            );
        }
        // §19.1, I8: the publishable document is the renderer output.
        "TX-12" => {
            let project = P::example();
            let build = project.build_ok();
            let build_id = build.build_id.expect("a build ID");
            let manifest: serde_json::Value = serde_json::from_slice(
                &std::fs::read(
                    project
                        .build_dir(&build_id)
                        .join("manifest.json")
                        .as_std_path(),
                )
                .expect("manifest"),
            )
            .expect("parses");
            let outputs = manifest["outputs"].as_array().expect("outputs");
            assert!(
                outputs
                    .iter()
                    .any(|row| { row["path"].as_str() == Some("modules/LexLeanExample/Main.tex") }),
                "the canonical document is a manifest output: {manifest}"
            );
            assert!(
                !outputs
                    .iter()
                    .any(|row| row["path"].as_str() == Some("src/Main.lex.tex")),
                "unchecked source bytes are never a published output"
            );
        }
        other => panic!("no latex-pdf case is wired for {other}"),
    }
}
