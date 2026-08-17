//! The `latex-pdf` suite: TX-01..TX-12.

use lexlean::artifact::content_id::Sha256Digest;
use lexlean::config::PdfProvider;

use crate::support::{self, P};

/// The §29.4 preamble, byte for byte.
const PREAMBLE: &str = "\\documentclass[11pt]{article}\n\\usepackage[T1]{fontenc}\n\\usepackage{amsmath}\n\\usepackage{amssymb}\n\\usepackage{amsthm}\n\\usepackage[hidelinks]{hyperref}\n\\newtheorem{theorem}{Theorem}[section]\n\\newtheorem{lemma}[theorem]{Lemma}\n\\newtheorem{corollary}[theorem]{Corollary}\n\\theoremstyle{definition}\n\\newtheorem{definition}[theorem]{Definition}\n\\begin{document}\n";

/// The §29.4 body of the literal example, byte for byte.
const EXAMPLE_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition}\n\\end{center}\n\\begin{theorem}\n\\label{ll:main:add-zero}\nFor every natural number \\(n\\), \\(n + 0 = n\\).\n\\end{theorem}\n\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}\n\\end{document}\n";

/// The exact canonical LaTeX body of [`support::FRAMES_MODULE`].
const FRAMES_TEX_BODY: &str = "\\begin{center}\n{\\LARGE Natural number addition: parity (order)}\n\\end{center}\n\\section{Natural number order-parity: sums}\n\\label{ll:main:frames}\n\\begin{definition}\n\\label{ll:main:even}\nFor every natural number \\(n\\), \\(n\\) is even holds exactly when there exists a natural number \\(k\\) such that \\(n = k + k\\).\n\\end{definition}\n\\begin{definition}\n\\label{ll:main:vanishes}\nFor every natural number \\(n\\), \\(n\\) vanishes holds exactly when \\(n = 0\\).\n\\end{definition}\n\\begin{definition}\n\\label{ll:main:precedes}\nFor every natural number \\(n\\) and natural number \\(m\\), \\(n\\) precedes \\(m\\) holds exactly when there exists a natural number \\(k\\) such that \\(n + k = m\\).\n\\end{definition}\n\\begin{definition}\n\\label{ll:main:double}\nFor every natural number \\(n\\), the double of \\(n\\) is defined as \\(n + n\\).\n\\end{definition}\n\\begin{definition}\n\\label{ll:main:total}\nFor every natural number \\(a\\) and natural number \\(b\\), the total of \\(a\\) and \\(b\\) is defined as \\(a + b\\).\n\\end{definition}\n\\begin{theorem}\n\\label{ll:main:double-even}\nFor every natural number \\(n\\), the double of \\(n\\) is even.\n\\end{theorem}\n\\begin{proof}\nUse \\(n\\) as the witness.\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:sum-even}\nFor every natural number \\(n\\), the sum of \\(n\\) and \\(n\\) is even.\n\\end{theorem}\n\\begin{proof}\nUse \\(n\\) as the witness.\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:total-even}\nFor every natural number \\(n\\), the total of \\(n\\) and \\(n\\) is even.\n\\end{theorem}\n\\begin{proof}\nUse \\(n\\) as the witness.\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:self-precedes}\nFor every natural number \\(n\\), \\(n\\) precedes \\(n\\).\n\\end{theorem}\n\\begin{proof}\nUse \\(0\\) as the witness.\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:successor-precedes}\nThe successor of \\(0\\) precedes the successor of the double of \\(0\\).\n\\end{theorem}\n\\begin{proof}\nUse \\(0\\) as the witness.\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:vanishes-conditional}\nFor every natural number \\(n\\), if \\(n\\) vanishes, then \\(n\\) precedes \\(n\\).\n\\end{theorem}\n\\begin{proof}\nAssume \\(h\\).\nUse \\(0\\) as the witness.\nThe goal follows by reflexivity.\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:even-and-precedes}\n\\(0\\) is even and \\(0\\) precedes \\(0\\).\n\\end{theorem}\n\\begin{proof}\nBranch \\(1\\):\n\\begin{quote}\nUse \\(0\\) as the witness.\nThe goal follows by reflexivity.\n\\end{quote}\nBranch \\(2\\):\n\\begin{quote}\nUse \\(0\\) as the witness.\nThe goal follows by reflexivity.\n\\end{quote}\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:bounded-self}\nFor every natural number \\(n\\), \\(n\\) is bounded by the successor of \\(n\\) or \\(n\\) is bounded by \\(n\\).\n\\end{theorem}\n\\begin{proof}\nSelect the right alternative.\nThe goal follows from \\(\\operatorname{lerefl}(n)\\).\n\\end{proof}\n\\begin{theorem}\n\\label{ll:main:cases-conjunction}\nFor every natural number \\(n\\), if \\(n\\) is even and \\(n\\) vanishes, then \\(n\\) precedes \\(n\\).\n\\end{theorem}\n\\begin{proof}\nAssume \\(h\\).\nConsider the cases of \\(h\\).\nCase \\(\\operatorname{andintro}\\) with \\(he\\), \\(hv\\):\n\\begin{quote}\nUse \\(0\\) as the witness.\nThe goal follows by reflexivity.\n\\end{quote}\n\\end{proof}\n\\end{document}\n";

/// The default stub provider body: records its working directory, its
/// listing, and its environment into the PDF stream.
const STUB_BODY: &str =
    "{ printf '%%PDF-fake\\n'; pwd; ls -A .; env | sort; } > \"$2/$name.pdf\"\n";

/// Install a stub PDF provider script whose compile step runs `body` (with
/// `$2` the output directory and `$name` the stem) and return its
/// configuration.
fn stub_provider(project: &P, body: &str, exit_code: i32) -> PdfProvider {
    let script = format!(
        "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then exit 0; fi\nname=$(basename \"$3\" .tex)\n{body}exit {exit_code}\n"
    );
    project.write("tools/fakepdf", &script);
    // The stub provider is a `#!/bin/sh` script, and the executable bit it
    // needs exists only on a unix host. Every caller reaches this through
    // `support::posix_shell_backed`, which reports the hosts that cannot run
    // one (§8.3, R2); the assertion names the gate for a caller that forgets
    // it, instead of failing later with an exec error that says nothing.
    assert!(
        support::posix_shell_host(),
        "the PDF-provider cases run a `#!/bin/sh` program: gate on support::posix_shell_backed"
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let script_path = project.root.join("tools/fakepdf");
        let mut permissions = std::fs::metadata(script_path.as_std_path())
            .expect("stat")
            .permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(script_path.as_std_path(), permissions).expect("chmod");
    }
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

fn fake_provider(project: &P, exit_code: i32) -> PdfProvider {
    stub_provider(project, STUB_BODY, exit_code)
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
        &lexlean::verify::child::Normalizer::default(),
    )
}

fn body_of(project: &P) -> String {
    support::tex_body(&support::tex_text(&support::rendered(project), "Main")).to_owned()
}

/// The Lean-verified fixture modules whose canonical LaTeX the suite
/// asserts, host-gated like every Lean-backed suite (§8.3): on a host with
/// the pinned toolchain each is verified once and its project reused; on a
/// platform-bound host without it the same modules render from linked IR
/// alone (rendering is platform independent) and the case says so.
enum Held {
    Verified(&'static P),
    Rendered(P),
}

impl Held {
    fn project(&self) -> &P {
        match self {
            Held::Verified(project) => project,
            Held::Rendered(project) => project,
        }
    }
}

struct Fixtures {
    frames: Held,
    corpus: Held,
    polish: Held,
}

fn fixtures(id: &str) -> Fixtures {
    if support::lean_backed(id) {
        let frames = support::verified_frames();
        let corpus = support::verified_corpus();
        let polish = support::verified_polish();
        for fixture in [frames, corpus, polish] {
            assert_eq!(
                fixture.attestation["status"], "verified",
                "the fixture attestation records success"
            );
        }
        Fixtures {
            frames: Held::Verified(&frames.project),
            corpus: Held::Verified(&corpus.project),
            polish: Held::Verified(&polish.project),
        }
    } else {
        Fixtures {
            frames: Held::Rendered(support::frames_project()),
            corpus: Held::Rendered(support::corpus_project()),
            polish: Held::Rendered(support::polish_project()),
        }
    }
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
            assert_eq!(first, format!("{PREAMBLE}{EXAMPLE_BODY}"), "§29.4 bytes");
        }
        // §19.2: the exact preamble, no host or timestamp metadata.
        "TX-02" => {
            for tex in [
                support::tex_text(&support::rendered(&P::example()), "Main"),
                support::tex_text(&support::rendered(&support::defs_project()), "Main"),
            ] {
                assert!(
                    tex.starts_with(PREAMBLE),
                    "the §29.4 preamble opens every module: {tex}"
                );
                for forbidden in ["\\today", "\\date", "hostname", "%"] {
                    assert!(!tex.contains(forbidden), "no host, time, or comment: {tex}");
                }
            }
        }
        // §19.4: canonical proposition and definition renderings, exactly.
        "TX-03" => {
            assert_eq!(body_of(&P::example()), EXAMPLE_BODY);
            assert_eq!(body_of(&support::defs_project()), support::DEFS_TEX_BODY);
            let unique = support::ext_project(support::UNIQUE_MODULE);
            assert_eq!(body_of(&unique), support::UNIQUE_TEX_BODY);
            let lre = support::ext_project(support::LRE_MODULE);
            assert_eq!(
                body_of(&lre),
                support::LRE_TEX_BODY,
                "LRE sup, sub, and frac lower to `^{{}}`, `_{{}}`, and `\\frac{{}}{{}}`"
            );
            // §13.4 text frames render as canonical prose in statements and
            // definition heads over a Lean-verified module: adjective,
            // intransitive, transitive, noun-of, and binary-noun-of, with
            // math arguments as islands and noun-phrase arguments nested,
            // and a text render template honored over the fixed pattern.
            let fixtures = fixtures("TX-03");
            assert_eq!(body_of(fixtures.frames.project()), FRAMES_TEX_BODY);
            // A section parameter typed by a text-only type noun renders
            // the noun's canonical word (`\text{kind}`), never a qualified
            // selector; a quantified proposition in trailing position (the
            // `have` statement, the right operand of a connective) is
            // prose; a document reference no entry names is
            // `\texttt{Module::component}` under its reference origin.
            let polish_body = body_of(fixtures.polish.project());
            assert_eq!(polish_body, support::POLISH_TEX_BODY);
            let corpus_body = body_of(fixtures.corpus.project());
            assert!(
                corpus_body.contains(
                    "\n0 + (n + 0) &= n + 0 && \\text{by } \\texttt{Main::zero-add}(n + 0) \\\\\n"
                ),
                "an applied reference in a calculation justification: {corpus_body}"
            );
            assert!(
                polish_body.contains(
                    "For every natural number \\(n\\), \\(n = n\\) or there exists a natural number \\(m\\) such that \\(n = m\\).\n"
                ),
                "a trailing existential stays prose, exactly as the source spells it: {polish_body}"
            );
            assert!(
                polish_body.contains(
                    "\nWe first establish for every natural number \\(k\\), \\(0 + k = k\\).\n"
                ),
                "the established proposition is prose: {polish_body}"
            );
            for body in [&polish_body, &corpus_body] {
                assert!(
                    !body.contains("\\operatorname{zero_add}") && !body.contains("_add}"),
                    "no Lean name with `_` inside math: {body}"
                );
            }
            let polish_build = support::rendered(fixtures.polish.project());
            let reference_rows: Vec<_> = polish_build.modules[0]
                .coverage
                .latex
                .iter()
                .filter(|row| {
                    row.origin
                        == lexlean::source::coverage::Origin::Reference {
                            module: "Main".to_owned(),
                            component: "zero-add".to_owned(),
                        }
                })
                .collect();
            assert_eq!(reference_rows.len(), 1, "one reference row");
            let row = reference_rows[0];
            assert_eq!(
                &polish_build.modules[0].tex_text[row.byte_start..row.byte_end],
                "Main::zero-add",
                "the reference row covers exactly `Module::component`"
            );

            // §15.1 admits `_` in a module segment, and a `\texttt`
            // reference is set in text mode inside a math island, where a
            // raw `_` is a hard TeX error. Every emitted byte keeps an
            // origin: the name's runs stay under the reference origin and
            // the escape is the registered `underscore` token.
            let underscored = support::underscore_module_project();
            let build = support::rendered(&underscored);
            let module = &build.modules[0];
            assert!(
                module.tex_text.contains("\\texttt{Main\\_x::zero-add}"),
                "the module segment's `_` is escaped: {}",
                module.tex_text
            );
            assert!(
                !module.tex_text.contains("Main_x"),
                "no raw `_` reaches the document: {}",
                module.tex_text
            );
            lexlean::backend::check_output_closure(&module.tex_text, &module.coverage.latex)
                .expect("closure");
            let escaped = "Main\\_x::zero-add";
            let at = module
                .tex_text
                .find(escaped)
                .expect("the escaped reference");
            let reference_origin = lexlean::source::coverage::Origin::Reference {
                module: support::UNDERSCORE_MODULE.to_owned(),
                component: "zero-add".to_owned(),
            };
            let covering: Vec<(String, lexlean::source::coverage::Origin)> = module
                .coverage
                .latex
                .iter()
                .filter(|row| row.byte_start >= at && row.byte_end <= at + escaped.len())
                .map(|row| {
                    (
                        module.tex_text[row.byte_start..row.byte_end].to_owned(),
                        row.origin.clone(),
                    )
                })
                .collect();
            assert_eq!(
                covering,
                vec![
                    ("Main".to_owned(), reference_origin.clone()),
                    (
                        "\\_".to_owned(),
                        lexlean::source::coverage::Origin::RendererToken("underscore".to_owned())
                    ),
                    ("x::zero-add".to_owned(), reference_origin),
                ],
                "each run keeps the reference origin and the escape is a registered token"
            );
        }
        // §19.5: proof prose from proof IR with fixed core forms: every
        // variant, branches visible, calculations aligned.
        "TX-04" => {
            let tex = support::tex_text(&support::rendered(&P::example()), "Main");
            assert!(
                tex.contains("\\begin{proof}\nThe goal follows by reflexivity.\n\\end{proof}"),
                "the canonical proof block: {tex}"
            );
            let project = P::example();
            project.write("src/Main.lex.tex", support::PROOF_FORMS_MODULE);
            assert_eq!(body_of(&project), support::PROOF_FORMS_TEX_BODY);
            let unique = support::ext_project(support::UNIQUE_MODULE);
            assert_eq!(body_of(&unique), support::UNIQUE_TEX_BODY);
            // Case labels name the constructor by its canonical form: a
            // constructor with surface arguments is an operator name in
            // math, an atom its plain surface; introduced locals are math
            // islands. Proof prose over the Lean-verified frames module.
            let fixtures = fixtures("TX-04");
            let frames_body = body_of(fixtures.frames.project());
            assert_eq!(frames_body, FRAMES_TEX_BODY);
            assert!(
                frames_body.contains(
                    "Consider the cases of \\(h\\).\nCase \\(\\operatorname{andintro}\\) with \\(he\\), \\(hv\\):\n"
                ),
                "the case label of a core constructor: {frames_body}"
            );
            let corpus_body = body_of(fixtures.corpus.project());
            assert!(
                corpus_body
                    .contains("\nCase \\(\\operatorname{cintro}\\) with \\(l\\), \\(r\\):\n"),
                "the case label of a glossary structure constructor: {corpus_body}"
            );
            assert!(
                corpus_body.contains("\nCase zero:\n")
                    && corpus_body.contains("\nCase \\(\\operatorname{succ}\\) with \\("),
                "atom and operator constructors: {corpus_body}"
            );
        }
        // §19.3: exact document structure, numbering, labels, sections
        // three deep, and parameters.
        "TX-05" => {
            assert_eq!(body_of(&P::example()), EXAMPLE_BODY);
            // Phrase punctuation (§15.3) is spaced as canonical source
            // spells it: no space before `:` or `)`, none after `(`, and a
            // tight hyphen; a noun-of term phrase in a heading is prose.
            let fixtures = fixtures("TX-05");
            let frames_body = body_of(fixtures.frames.project());
            assert_eq!(frames_body, FRAMES_TEX_BODY);
            assert!(
                frames_body.contains("{\\LARGE Natural number addition: parity (order)}\n"),
                "title punctuation: {frames_body}"
            );
            assert!(
                frames_body.contains(
                    "\\section{Natural number order-parity: sums}\n\\label{ll:main:frames}\n"
                ),
                "heading punctuation: {frames_body}"
            );
            let project = support::frames_project();
            project.edit(
                "src/Main.lex.tex",
                "\\heading{Natural number order - parity: sums}",
                "\\heading{Natural number order (the successor of \\(0\\)): sums}",
            );
            let heading_body = body_of(&project);
            assert!(
                heading_body
                    .contains("\\section{Natural number order (the successor of \\(0\\)): sums}\n"),
                "a heading term phrase renders as prose: {heading_body}"
            );
            let project = P::example();
            project.write("src/Main.lex.tex", support::SECTIONS_MODULE);
            assert_eq!(body_of(&project), support::SECTIONS_TEX_BODY);
            assert!(
                support::SECTIONS_TEX_BODY
                    .contains("\\textbf{Natural number addition}\n\\label{ll:main:inner}"),
                "the third level is the registered bold construct"
            );
            assert!(
                !support::SECTIONS_TEX_BODY.contains("\\mathrm{Natural"),
                "no math-mode heading"
            );
        }
        // §19.6: complete output lexical coverage, mechanically closed.
        "TX-06" => {
            for project in [
                P::example(),
                support::defs_project(),
                support::ext_project(support::LRE_MODULE),
                {
                    let project = P::example();
                    project.write("src/Main.lex.tex", support::PROOF_FORMS_MODULE);
                    project
                },
                support::frames_project(),
                support::corpus_project(),
                support::polish_project(),
            ] {
                let build = support::rendered(&project);
                let module = &build.modules[0];
                lexlean::backend::check_output_closure(&module.tex_text, &module.coverage.latex)
                    .expect("closure");
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
                for row in &module.coverage.latex {
                    if let lexlean::source::coverage::Origin::Metadata { owner } = &row.origin {
                        assert!(
                            !matches!(owner.as_str(), "core:lean-syntax/1"),
                            "no sort renders as metadata"
                        );
                    }
                }
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
            // The package locks (its bytes are inputs); building the
            // glossary closure rejects the unregistered token (§13.9).
            project.relock();
            let error = project.check_err();
            support::expect_code(&error, "LLR3004");

            // §13.5 rule 5 admits a non-ASCII glyph in a canonical *source*
            // form, but §19.1 produces every mathematical construct through
            // LRE and the registry, and the fixed §19.2 preamble cannot
            // typeset a raw scalar: TeX drops it with a `Missing character`
            // log line and the glyph vanishes from the published document.
            // An entry whose LRE renders its own Unicode surface is
            // refused, naming the entry, the form, and the scalar.
            let unicode = support::unicode_surface_project();
            let error = unicode
                .engine()
                .build(lexlean::BuildRequest {
                    selection: lexlean::Selection::Entrypoints,
                })
                .err()
                .expect("a raw Unicode surface never reaches the document");
            support::expect_code(&error, "LLB6002");
            let message = &error.diagnostics[0].message;
            assert!(
                message.contains("test.unicode::voidset")
                    && message.contains("voidset")
                    && message.contains('\u{2205}')
                    && message.contains("renderer token"),
                "the refusal names the entry, the form, the scalar, and the fix: {message}"
            );
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
        // §19.7: hash-checked, shell-free, isolated execution with exact
        // resources, timeout, output cap, and exactly one output.
        "TX-09" => {
            if !support::posix_shell_backed("TX-09") {
                return;
            }
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
            // canonical TeX and an isolated environment.
            provider.program_sha256 = correct;
            let result = support::with_env(
                &[
                    ("HTTP_PROXY", Some("http://proxy.invalid")),
                    ("LEXLEAN_TEST_LEAK", Some("leaked")),
                ],
                || run_fake_provider(&project, &provider).expect("the provider runs"),
            );
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
                .take_while(|line| !line.contains('='))
                .filter(|line| !line.is_empty())
                .collect();
            assert_eq!(
                listing,
                vec!["LexLeanExample.Main.tex"],
                "the provider sees exactly the canonical TeX: {recorded}"
            );
            let env_lines: Vec<&str> = recorded.lines().filter(|line| line.contains('=')).collect();
            assert!(
                !env_lines.iter().any(|line| line.starts_with("HTTP_PROXY=")),
                "no inherited proxy variable: {env_lines:?}"
            );
            assert!(
                !env_lines
                    .iter()
                    .any(|line| line.starts_with("LEXLEAN_TEST_LEAK=")),
                "no inherited arbitrary variable: {env_lines:?}"
            );
            let home = env_lines
                .iter()
                .find_map(|line| line.strip_prefix("HOME="))
                .expect("a HOME");
            assert!(
                home.contains("/.lexlean/") && home.ends_with("/home"),
                "a temporary HOME: {home}"
            );
            assert_eq!(result.version.exit_code, 0);
            assert_eq!(result.compile.exit_code, 0);
            // The working directory is the provider's own `pwd`, which
            // resolves every symlink on the way (macOS reaches its temporary
            // directories through `/var -> private/var`), while the argv is
            // the path LexLean constructed. They denote one directory; only
            // canonicalizing both compares that rather than the host's
            // spelling.
            assert_eq!(result.compile.argv.len(), 3, "three whole arguments");
            assert_eq!(result.compile.argv[0], "--outdir");
            assert_eq!(result.compile.argv[2], "LexLeanExample.Main.tex");
            // The staging tree is gone by now, so the two spellings are
            // compared as text: they agree exactly, or the provider's
            // resolved one ends with the constructed one, which is what a
            // symlinked prefix leaves behind.
            let expected_out = format!("{}/out", workdir.trim_end_matches("/work"));
            let constructed = &result.compile.argv[1];
            assert!(
                *constructed == expected_out
                    || expected_out.ends_with(constructed.trim_start_matches('/')),
                "the `{{out_dir}}` placeholder expanded to the output directory: {constructed} against {expected_out}"
            );

            // Declared resources are copied by basename next to the TeX.
            project.write("assets/logo.dat", "logo");
            project.write("assets/style.sty", "sty");
            provider.resources = vec!["assets/logo.dat".to_owned(), "assets/style.sty".to_owned()];
            let result = run_fake_provider(&project, &provider).expect("resources run");
            let recorded = String::from_utf8_lossy(&result.pdf_bytes).into_owned();
            let listing: Vec<&str> = recorded
                .lines()
                .skip(2)
                .take_while(|line| !line.contains('='))
                .filter(|line| !line.is_empty())
                .collect();
            assert_eq!(
                listing,
                vec!["LexLeanExample.Main.tex", "logo.dat", "style.sty"],
                "declared resources are staged: {recorded}"
            );
            // A resource basename collision, or a collision with the TeX
            // itself, is refused.
            project.write("other/logo.dat", "other");
            provider.resources = vec!["assets/logo.dat".to_owned(), "other/logo.dat".to_owned()];
            let error = run_fake_provider(&project, &provider).expect_err("collision");
            assert_eq!(error.code.as_str(), "LLB6004");
            assert!(error.message.contains("logo.dat"), "{}", error.message);
            project.write("assets/LexLeanExample.Main.tex", "clobber");
            provider.resources = vec!["assets/LexLeanExample.Main.tex".to_owned()];
            let error = run_fake_provider(&project, &provider).expect_err("tex collision");
            assert_eq!(error.code.as_str(), "LLB6004");
            provider.resources = Vec::new();

            // The output must be a bare file name.
            for bad in ["../{stem}.pdf", "sub/{stem}.pdf", "..", "a\\b.pdf"] {
                let mut escaping = provider.clone();
                escaping.output = bad.to_owned();
                let error = run_fake_provider(&project, &escaping).expect_err("bare name");
                assert_eq!(error.code.as_str(), "LLB6004", "`{bad}` is refused");
            }
            // And it is refused when the configuration is loaded, not only
            // when a provider eventually runs: an output that can never
            // satisfy the protocol is a configuration error (§19.7).
            for bad in ["../{stem}.pdf", "sub/{stem}.pdf"] {
                let configured = P::example();
                configured.edit(
                    "lexlean.toml",
                    "\n[limits]",
                    &format!(
                        "\n[pdf]\nmode = \"external\"\nprogram = \"tools/fakepdf\"\nprogram_sha256 = \"{}\"\nversion_argv = [\"--version\"]\nversion_stdout_sha256 = \"{}\"\ncompile_argv = [\"--outdir\", \"{{out_dir}}\", \"{{input}}\"]\noutput = \"{bad}\"\nresources = []\n\n[limits]",
                        Sha256Digest::of(b"").to_hex(),
                        Sha256Digest::of(b"\n").to_hex(),
                    ),
                );
                let error = lexlean::Engine::load(&configured.root.join("lexlean.toml"))
                    .err()
                    .unwrap_or_else(|| panic!("`{bad}` is refused at load"));
                support::expect_code(&error, "LLC0101");
                assert!(
                    format!("{error}").contains("bare file name"),
                    "the failure says why: {error}"
                );
            }

            // Exactly one output: an extra file in the output directory
            // fails and is named.
            let extra = stub_provider(
                &project,
                "printf '%%PDF-x' > \"$2/$name.pdf\"; printf 'log' > \"$2/$name.log\"\n",
                0,
            );
            let error = run_fake_provider(&project, &extra).expect_err("extra output");
            assert_eq!(error.code.as_str(), "LLB6004");
            assert!(
                error.message.contains("LexLeanExample.Main.log"),
                "the extra entry is named: {}",
                error.message
            );
            // No output at all fails.
            let none = stub_provider(&project, "true\n", 0);
            let error = run_fake_provider(&project, &none).expect_err("no output");
            assert_eq!(error.code.as_str(), "LLB6004");
            // A non-PDF stream fails.
            let not_pdf = stub_provider(&project, "printf 'hello' > \"$2/$name.pdf\"\n", 0);
            let error = run_fake_provider(&project, &not_pdf).expect_err("not a pdf");
            assert_eq!(error.code.as_str(), "LLB6004");

            // The output cap (`max_child_output_bytes`) bounds the PDF.
            let capped = P::example();
            capped.edit(
                "lexlean.toml",
                "max_child_output_bytes = 16777216",
                "max_child_output_bytes = 64",
            );
            capped.relock();
            let big = stub_provider(
                &capped,
                "{ printf '%%PDF-'; head -c 200 /dev/zero; } > \"$2/$name.pdf\"\n",
                0,
            );
            let error = run_fake_provider(&capped, &big).expect_err("too big");
            assert_eq!(error.code.as_str(), "LLS8002");
            assert!(
                error.message.contains("max_child_output_bytes"),
                "{}",
                error.message
            );
            let small = stub_provider(&capped, "printf '%%PDF-small' > \"$2/$name.pdf\"\n", 0);
            run_fake_provider(&capped, &small).expect("within the cap");

            // The child timeout is enforced.
            let slow = P::example();
            slow.edit(
                "lexlean.toml",
                "child_timeout_ms = 300000",
                "child_timeout_ms = 200",
            );
            slow.relock();
            let sleeper = stub_provider(&slow, "sleep 5\nprintf '%%PDF-' > \"$2/$name.pdf\"\n", 0);
            let started = std::time::Instant::now();
            let error = run_fake_provider(&slow, &sleeper).expect_err("timeout");
            assert_eq!(error.code.as_str(), "LLS8002");
            assert!(
                error.message.contains("child_timeout_ms"),
                "{}",
                error.message
            );
            assert!(
                started.elapsed() < std::time::Duration::from_secs(4),
                "the child was killed at the deadline"
            );
        }
        // §19.8: the recipe ID and the PDF hash are independent records.
        "TX-10" => {
            if !support::posix_shell_backed("TX-10") {
                return;
            }
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
            if !support::posix_shell_backed("TX-11") {
                return;
            }
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
            // A configured provider records one row and two process records
            // per module in the attestation, and the PDF lands only in the
            // verified set.
            let Some(verified) = support::verify_ok_backed("TX-11", &with_pdf) else {
                return;
            };
            let attestation: serde_json::Value = serde_json::from_slice(
                &std::fs::read(verified.root.join("attestation.json").as_std_path()).expect("read"),
            )
            .expect("parses");
            // §19.7 step 4, §25.6: the provider's isolated directory is a
            // sibling of the verification staging tree, never inside it —
            // an untrusted external program that walks out of its working
            // directory must not reach the artifacts being staged. The
            // published set is the fixed §22.8 one, with no provider
            // scratch in it.
            let published = support::file_set(&verified.root);
            assert!(
                published
                    .iter()
                    .all(|name| !name.contains("work/") && !name.contains("home/")),
                "no provider scratch is published: {published:?}"
            );

            let pdf = attestation["pdf"].as_array().expect("pdf rows");
            assert_eq!(pdf.len(), 1);
            assert_eq!(pdf[0]["module"].as_str(), Some("LexLeanExample.Main"));
            assert_eq!(pdf[0]["version"]["tool"].as_str(), Some("pdf"));
            assert_eq!(pdf[0]["compile"]["tool"].as_str(), Some("pdf"));
            let pdf_processes = attestation["processes"]
                .as_array()
                .expect("processes")
                .iter()
                .filter(|row| row["tool"].as_str() == Some("pdf"))
                .count();
            assert_eq!(pdf_processes, 2, "version and compile records");
            assert!(verified
                .root
                .join("pdf/LexLeanExample.Main.pdf")
                .as_std_path()
                .is_file());
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
