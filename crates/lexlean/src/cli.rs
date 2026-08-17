//! The command-line interface (SPEC.md §23): exact commands, exact exit
//! codes, and the two diagnostic output modes. No environment variable
//! changes semantic configuration (CL-17).

use std::collections::BTreeSet;
use std::io::Write;

use camino::{Utf8Path, Utf8PathBuf};
use clap::{Parser, Subcommand, ValueEnum};

use crate::api::{
    command_result_json, BuildRequest, CheckRequest, CleanResult, CommandIds, Engine,
    FormatRequest, LockRequest, Selection, VerifyRequest,
};
use crate::code;
use crate::config::{is_module_segment, is_project_name, LexiconSource, Limits, ProjectConfig};
use crate::diagnostic::Diagnostic;
use crate::error::LexLeanError;

/// The diagnostic output modes (§20.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum DiagnosticFormat {
    /// Deterministic text to stderr.
    Human,
    /// One canonical JSON command-result object to stdout.
    Json,
}

/// The color modes; ignored for JSON (§23.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum ColorMode {
    /// Color when the stream is a terminal.
    Auto,
    /// Always color.
    Always,
    /// Never color.
    Never,
}

#[derive(Parser)]
#[command(
    name = "lexlean",
    disable_version_flag = true,
    about = "A closed-lexicon LaTeX-to-Lean 4 compiler whose canonical document and prose-free Lean program are generated from one semantic representation."
)]
struct Cli {
    /// The project configuration file; defaults to lexlean.toml discovered
    /// upward.
    #[arg(long, global = true)]
    project: Option<Utf8PathBuf>,
    /// The diagnostic output mode.
    #[arg(long, global = true, value_enum, default_value = "human")]
    diagnostic_format: DiagnosticFormat,
    /// The color mode; ignored for json.
    #[arg(long, global = true, value_enum, default_value = "auto")]
    color: ColorMode,
    /// Report the compiler, language, semantics ID, and Lean toolchain.
    #[arg(long)]
    version: bool,
    #[command(subcommand)]
    command: Option<CommandKind>,
}

#[derive(Subcommand)]
enum CommandKind {
    /// Create a new project in an absent or empty directory.
    Init {
        /// The destination directory.
        path: Option<Utf8PathBuf>,
        /// The project name.
        #[arg(long)]
        name: String,
        /// The Lean module prefix.
        #[arg(long)]
        module_prefix: String,
    },
    /// Update or check the lock file.
    Lock {
        /// Exact-byte check instead of updating.
        #[arg(long)]
        check: bool,
        /// Permit acquiring missing exact Git commits.
        #[arg(long)]
        allow_network: bool,
    },
    /// Check a selection through linked IR.
    Check {
        /// Every module beneath every source root.
        #[arg(long)]
        all: bool,
        /// Explicit input modules.
        inputs: Vec<Utf8PathBuf>,
    },
    /// Build a selection to the fixed content-addressed layout.
    Build {
        /// Every module beneath every source root.
        #[arg(long)]
        all: bool,
        /// Explicit input modules.
        inputs: Vec<Utf8PathBuf>,
    },
    /// Verify a selection through the complete fixed pipeline.
    Verify {
        /// Every module beneath every source root.
        #[arg(long)]
        all: bool,
        /// Explicit input modules.
        inputs: Vec<Utf8PathBuf>,
    },
    /// Rewrite canonical source, or exact-byte compare.
    Fmt {
        /// Exact-byte check instead of rewriting.
        #[arg(long)]
        check: bool,
        /// Every module beneath every source root.
        #[arg(long)]
        all: bool,
        /// Explicit input modules.
        inputs: Vec<Utf8PathBuf>,
    },
    /// Remove the configured build root.
    Clean,
    /// Print the registered entry for one diagnostic code.
    Explain {
        /// The diagnostic code.
        code: String,
    },
}

/// The command names, in the order of §23.4.
const COMMAND_NAMES: [&str; 8] = [
    "init", "lock", "check", "build", "verify", "fmt", "clean", "explain",
];

/// The embedded diagnostic registry, for `explain` (§23.4). The registry
/// file is the single source (R1); the binary carries a copy.
const ERRORS_TOML: &str = include_str!(concat!(env!("OUT_DIR"), "/errors.toml"));

/// The default explicit resource policy written by `init` (§10.1's
/// schema example).
const INIT_LIMITS: Limits = Limits {
    max_file_bytes: 4_194_304,
    max_total_source_bytes: 67_108_864,
    max_primitive_atoms: 2_000_000,
    max_token_lattice_edges: 4_000_000,
    max_parse_states: 4_000_000,
    max_ir_nodes: 2_000_000,
    max_scope_depth: 1024,
    max_import_depth: 128,
    max_diagnostics: 256,
    max_child_output_bytes: 16_777_216,
    child_timeout_ms: 300_000,
};

/// `"1 module"` or `"3 modules"`: a summary that says "1 modules" reads as a
/// defect in the tool that printed it, and §24.2 already refuses to treat a
/// multi-module operation as singular anywhere else.
fn canonical(count: usize) -> String {
    if count == 1 {
        "1 module is".to_owned()
    } else {
        format!("{count} modules are")
    }
}

fn modules(count: usize) -> String {
    if count == 1 {
        "1 module".to_owned()
    } else {
        format!("{count} modules")
    }
}

fn usage_error(message: impl Into<String>) -> LexLeanError {
    LexLeanError::from_diagnostic(Diagnostic::new(code!("LLC0001"), message))
}

fn selection_from(all: bool, inputs: Vec<Utf8PathBuf>) -> Result<Selection, LexLeanError> {
    match (all, inputs.is_empty()) {
        (true, true) => Ok(Selection::All),
        (true, false) => Err(LexLeanError::from_diagnostic(Diagnostic::new(
            code!("LLC0002"),
            "--all and explicit inputs are mutually exclusive",
        ))),
        (false, true) => Ok(Selection::Entrypoints),
        (false, false) => {
            // The same input given twice is a duplicate selection (§23.3),
            // reported rather than silently collapsed into the set.
            let mut seen: BTreeSet<&Utf8PathBuf> = BTreeSet::new();
            for input in &inputs {
                if !seen.insert(input) {
                    return Err(LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLC0002"),
                        format!("input `{input}` is given more than once"),
                    )));
                }
            }
            Ok(Selection::Files(inputs.into_iter().collect()))
        }
    }
}

/// SGR wrapping for human diagnostics; empty strings when color is off.
struct Palette {
    bold_red: &'static str,
    bold: &'static str,
    cyan: &'static str,
    reset: &'static str,
}

impl Palette {
    const COLOR: Self = Self {
        bold_red: "\u{1b}[1;31m",
        bold: "\u{1b}[1m",
        cyan: "\u{1b}[36m",
        reset: "\u{1b}[0m",
    };
    const PLAIN: Self = Self {
        bold_red: "",
        bold: "",
        cyan: "",
        reset: "",
    };
}

fn palette(mode: ColorMode) -> &'static Palette {
    use std::io::IsTerminal;
    match mode {
        ColorMode::Always => &Palette::COLOR,
        ColorMode::Never => &Palette::PLAIN,
        // `auto` colors a terminal stderr only; NO_COLOR is a presentation
        // convention, never semantic configuration.
        ColorMode::Auto => {
            if std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none() {
                &Palette::COLOR
            } else {
                &Palette::PLAIN
            }
        }
    }
}

fn print_human_diagnostics(stderr: &mut dyn Write, error: &LexLeanError, colors: &Palette) {
    for diagnostic in &error.diagnostics {
        let _ = write!(
            stderr,
            "{}error{}[{}]: {}{}{}",
            colors.bold_red,
            colors.reset,
            diagnostic.code.as_str(),
            colors.bold,
            diagnostic.message,
            colors.reset
        );
        if let Some(span) = &diagnostic.primary {
            let _ = write!(
                stderr,
                "\n  {}-->{} {}:{}:{}",
                colors.cyan, colors.reset, span.path, span.line_start, span.column_start
            );
        }
        let _ = writeln!(stderr);
        for label in &diagnostic.labels {
            let _ = writeln!(
                stderr,
                "  label: {} ({}:{}:{})",
                label.message, label.span.path, label.span.line_start, label.span.column_start
            );
        }
        for note in &diagnostic.notes {
            let _ = writeln!(stderr, "  note: {}", note.message);
        }
        for help in &diagnostic.help {
            let _ = writeln!(stderr, "  help: {help}");
        }
        for cause in &diagnostic.causes {
            let _ = writeln!(stderr, "  cause: {cause}");
        }
    }
}

fn version_text() -> String {
    format!(
        "lexlean {}\nlanguage {}\ncompiler-semantics {}\nlean-toolchain {}\n",
        crate::COMPILER_VERSION,
        crate::LANGUAGE_VERSION,
        crate::compiler_semantics_id().to_hex(),
        crate::LEAN_TOOLCHAIN
    )
}

/// The generated `ERRORS.md` entry for one registered code (§23.4).
#[must_use]
pub fn explain_text(requested: &str) -> Option<String> {
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Row {
        code: String,
        class: String,
        exit: u8,
        title: String,
        statement: String,
    }
    #[derive(serde::Deserialize)]
    struct Loose {
        #[allow(dead_code)]
        spec: String,
        #[serde(rename = "error")]
        errors: Vec<Row>,
    }
    let registry: Loose = toml::from_str(ERRORS_TOML).ok()?;
    registry
        .errors
        .iter()
        .find(|row| row.code == requested)
        .map(|row| {
            format!(
                "## `{}` --- {}\n\n{}\n\nClass: `{}`. Exit code: {}.\n",
                row.code, row.title, row.statement, row.class, row.exit
            )
        })
}

/// Pre-scan argv for `--diagnostic-format json` (§20.6), so even a usage
/// error is reported inside the one JSON result object.
fn wants_json(arguments: &[String]) -> bool {
    let mut previous: Option<&str> = None;
    for argument in arguments.iter().skip(1) {
        if argument == "--diagnostic-format=json" {
            return true;
        }
        if previous == Some("--diagnostic-format") && argument == "json" {
            return true;
        }
        previous = Some(argument.as_str());
    }
    false
}

/// The subcommand named on argv, when any, for the JSON `command` field
/// of a usage failure.
fn named_command(arguments: &[String]) -> &'static str {
    arguments
        .iter()
        .skip(1)
        .find_map(|argument| COMMAND_NAMES.iter().find(|name| **name == argument))
        .copied()
        .unwrap_or("")
}

/// Everything one command run produces besides its exit code.
#[derive(Default)]
struct Outcome {
    modules: BTreeSet<String>,
    artifacts: Vec<String>,
    ids: CommandIds,
    summary: String,
    explanation: Option<String>,
}

/// Emit a finished command's result in the selected mode and return the
/// exit code.
fn emit(
    json_mode: bool,
    color: ColorMode,
    command_name: &str,
    outcome: &Outcome,
    result: Result<(), LexLeanError>,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> i32 {
    let (exit_code, error) = match result {
        Ok(()) => (0, None),
        Err(error) => (error.class.exit_code(), Some(error)),
    };
    if json_mode {
        let empty = Vec::new();
        let diagnostics = error.as_ref().map_or(&empty, |e| &e.diagnostics);
        let json = command_result_json(
            command_name,
            exit_code,
            &outcome.modules,
            &outcome.artifacts,
            diagnostics,
            &outcome.ids,
            outcome.explanation.as_deref(),
        );
        let _ = stdout.write_all(&json.to_file_bytes());
    } else {
        if exit_code == 0 {
            if let Some(explanation) = &outcome.explanation {
                let _ = write!(stdout, "{explanation}");
            } else if !outcome.summary.is_empty() {
                let _ = write!(stdout, "{}", outcome.summary);
            }
        }
        if let Some(error) = &error {
            print_human_diagnostics(stderr, error, palette(color));
        }
    }
    exit_code
}

/// Run the CLI against explicit argument and output streams; returns the
/// exact documented exit code (§23.6).
#[allow(clippy::too_many_lines)]
pub fn run(
    arguments: &[String],
    working_directory: &Utf8Path,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> i32 {
    let json_mode = wants_json(arguments);
    let parsed = match Cli::try_parse_from(arguments) {
        Ok(parsed) => parsed,
        Err(clap_error) => {
            use clap::error::ErrorKind;
            if matches!(
                clap_error.kind(),
                ErrorKind::DisplayHelp | ErrorKind::DisplayVersion
            ) {
                let _ = write!(stdout, "{clap_error}");
                return 0;
            }
            // Usage errors are LLC0001 (§26.3); in JSON mode they live
            // inside the result object and stderr stays empty (§23.7).
            // The parser's first line is the error; every further line
            // (usage, tips, the `--help` pointer) is help, one entry per
            // line, so the human rendering keeps the multi-line form.
            let rendered = clap_error.render().to_string();
            let mut lines = rendered
                .lines()
                .map(str::trim_end)
                .filter(|line| !line.is_empty());
            let message = lines.next().map_or_else(
                || "invalid command line".to_owned(),
                |line| line.strip_prefix("error: ").unwrap_or(line).to_owned(),
            );
            let mut diagnostic = Diagnostic::new(code!("LLC0001"), message);
            for line in lines {
                diagnostic = diagnostic.with_help(line.trim_start());
            }
            let error = LexLeanError::from_diagnostic(diagnostic);
            return emit(
                json_mode,
                ColorMode::Never,
                named_command(arguments),
                &Outcome::default(),
                Err(error),
                stdout,
                stderr,
            );
        }
    };
    if parsed.version {
        let _ = write!(stdout, "{}", version_text());
        return 0;
    }
    let color = parsed.color;
    let Some(command) = parsed.command else {
        return emit(
            json_mode,
            color,
            "",
            &Outcome::default(),
            Err(usage_error("a command is required; see --help")),
            stdout,
            stderr,
        );
    };
    let command_name = match &command {
        CommandKind::Init { .. } => "init",
        CommandKind::Lock { .. } => "lock",
        CommandKind::Check { .. } => "check",
        CommandKind::Build { .. } => "build",
        CommandKind::Verify { .. } => "verify",
        CommandKind::Fmt { .. } => "fmt",
        CommandKind::Clean => "clean",
        CommandKind::Explain { .. } => "explain",
    };

    let mut outcome = Outcome::default();
    let result: Result<(), LexLeanError> = (|| match command {
        CommandKind::Explain { code: requested } => match explain_text(&requested) {
            Some(text) => {
                outcome.explanation = Some(text);
                Ok(())
            }
            None => Err(usage_error(format!(
                "`{requested}` is not a registered diagnostic code"
            ))),
        },
        CommandKind::Init {
            path,
            name,
            module_prefix,
        } => {
            let (destination, shown) = match path {
                Some(given) if given.is_relative() => {
                    (working_directory.join(&given), given.to_string())
                }
                Some(given) => (given.clone(), given.to_string()),
                None => (working_directory.to_path_buf(), ".".to_owned()),
            };
            init_project(&destination, &name, &module_prefix)?;
            outcome.summary = format!("initialized {shown}\n");
            Ok(())
        }
        other => {
            let config_path = match &parsed.project {
                Some(explicit) => explicit.clone(),
                None => crate::project::discover(working_directory)?,
            };
            let engine = Engine::load(&config_path)?;
            match other {
                CommandKind::Lock {
                    check,
                    allow_network,
                } => {
                    let result = engine.lock(LockRequest {
                        check_only: check,
                        allow_network,
                    })?;
                    outcome.summary = if result.written {
                        format!("wrote {}\n", engine.project().config.lockfile)
                    } else {
                        format!("{} is current\n", engine.project().config.lockfile)
                    };
                    Ok(())
                }
                CommandKind::Check { all, inputs } => {
                    let result = engine.check(CheckRequest {
                        selection: selection_from(all, inputs)?,
                    })?;
                    outcome.modules = result.units.keys().cloned().collect();
                    outcome.ids.source_id = Some(result.source_id);
                    outcome.ids.semantic_id = Some(result.semantic_id);
                    outcome.summary = format!(
                        "checked {} (source {}, semantic {})\n",
                        modules(result.units.len()),
                        result.source_id.to_hex(),
                        result.semantic_id.to_hex()
                    );
                    Ok(())
                }
                CommandKind::Build { all, inputs } => {
                    let result = engine.build(BuildRequest {
                        selection: selection_from(all, inputs)?,
                    })?;
                    outcome.modules = result.units.keys().cloned().collect();
                    outcome.ids.source_id = Some(result.source_id);
                    outcome.ids.semantic_id = Some(result.semantic_id);
                    outcome.ids.build_id = result.build_id;
                    if let Some(id) = result.build_id {
                        let artifact = format!(
                            "{}/build/{}",
                            engine.project().config.build_root,
                            id.to_hex()
                        );
                        outcome.summary =
                            format!("built {} at {artifact}\n", modules(result.units.len()));
                        outcome.artifacts.push(artifact);
                    }
                    Ok(())
                }
                CommandKind::Verify { all, inputs } => {
                    let result = engine.verify(VerifyRequest {
                        selection: selection_from(all, inputs)?,
                    })?;
                    outcome.modules = result.units.keys().cloned().collect();
                    outcome.ids.source_id = Some(result.source_id);
                    outcome.ids.semantic_id = Some(result.semantic_id);
                    outcome.ids.build_id = Some(result.build_id);
                    outcome.ids.attestation_id = Some(result.attestation_id);
                    outcome.artifacts.push(format!(
                        "{}/verified/{}",
                        engine.project().config.build_root,
                        result.attestation_id.to_hex()
                    ));
                    outcome.summary = format!(
                        "verified {}; attestation {}\n",
                        modules(result.units.len()),
                        result.attestation_id.to_hex()
                    );
                    Ok(())
                }
                CommandKind::Fmt { check, all, inputs } => {
                    let result = engine.format(FormatRequest {
                        selection: selection_from(all, inputs)?,
                        check_only: check,
                    })?;
                    outcome.modules = result.units.keys().cloned().collect();
                    let rewritten = result.units.values().filter(|already| !**already).count();
                    outcome.summary = if check {
                        format!("{} canonical\n", canonical(result.units.len()))
                    } else {
                        format!("formatted {}\n", modules(rewritten))
                    };
                    Ok(())
                }
                CommandKind::Clean => {
                    let build_root = engine.project().config.build_root.clone();
                    outcome.summary = match engine.clean()? {
                        CleanResult::Removed => format!("removed {build_root}\n"),
                        CleanResult::Absent => {
                            format!("nothing to remove: {build_root} does not exist\n")
                        }
                    };
                    Ok(())
                }
                CommandKind::Init { .. } | CommandKind::Explain { .. } => {
                    unreachable!("handled above")
                }
            }
        }
    })();

    emit(
        json_mode,
        color,
        command_name,
        &outcome,
        result,
        stdout,
        stderr,
    )
}

/// The Lake manifest `init` writes (§23.4): the shape Lake itself writes
/// for a dependency-free workspace, so `lake env` never rewrites the
/// workspace files pinned by the lock (§10.4, §22.2).
fn lake_manifest_text(lake_name: &str) -> String {
    format!(
        "{{\"version\": \"1.2.0\",\n \"packagesDir\": \".lake/packages\",\n \"packages\": [],\n \"name\": \"{lake_name}\",\n \"lakeDir\": \".lake\",\n \"fixedToolchain\": false}}\n"
    )
}

/// Create a new project skeleton (§23.4): only in an absent or empty
/// directory, never overwriting; the inputs are validated before anything
/// is written, and any later failure removes everything init created.
fn init_project(
    destination: &Utf8Path,
    name: &str,
    module_prefix: &str,
) -> Result<(), LexLeanError> {
    if !is_project_name(name) {
        return Err(usage_error(format!(
            "`{name}` is not a valid project name: `[a-z][a-z0-9-]{{0,62}}` (§10.1)"
        )));
    }
    if module_prefix.is_empty() || !module_prefix.split('.').all(is_module_segment) {
        return Err(usage_error(format!(
            "`{module_prefix}` is not a valid module prefix: dot-separated `[A-Z][A-Za-z0-9_]*` segments (§10.1)"
        )));
    }
    let host_lib = format!("{}Host", module_prefix.replace('.', ""));
    let lake_name = format!("{}_host", name.replace('-', "_"));
    let config = ProjectConfig {
        name: name.to_owned(),
        module_prefix: module_prefix.to_owned(),
        source_roots: vec!["src".to_owned()],
        entrypoints: vec!["src/Main.lex.tex".to_owned()],
        build_root: ".lexlean".to_owned(),
        lockfile: "lexlean.lock".to_owned(),
        lean_workspace: ".".to_owned(),
        lexicon_sources: vec![LexiconSource::Builtin {
            package: "lexlean.std.nat".to_owned(),
        }],
        limits: INIT_LIMITS,
        pdf: None,
    };
    let files: Vec<(String, Vec<u8>)> = vec![
        ("lexlean.toml".to_owned(), config.canonical_toml().into_bytes()),
        (
            "lean-toolchain".to_owned(),
            format!("{}\n", crate::LEAN_TOOLCHAIN).into_bytes(),
        ),
        (
            "lakefile.toml".to_owned(),
            format!(
                "name = \"{lake_name}\"\nversion = \"0.1.0\"\ndefaultTargets = [\"{host_lib}\"]\n\n[[lean_lib]]\nname = \"{host_lib}\"\n"
            )
            .into_bytes(),
        ),
        (
            "lake-manifest.json".to_owned(),
            lake_manifest_text(&lake_name).into_bytes(),
        ),
        (format!("{host_lib}.lean"), b"module\nimport Init\n".to_vec()),
        (
            "src/Main.lex.tex".to_owned(),
            b"\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{addition}\n\\end{lexlean}\n"
                .to_vec(),
        ),
        (".gitignore".to_owned(), b"/.lexlean/\n/.lake/\n".to_vec()),
    ];

    let created_destination = match std::fs::symlink_metadata(destination.as_std_path()) {
        Ok(metadata) => {
            if !metadata.is_dir() {
                return Err(usage_error(format!(
                    "{destination} exists and is not a directory; init never overwrites"
                )));
            }
            let mut entries = std::fs::read_dir(destination.as_std_path())
                .map_err(|io_error| usage_error(format!("{destination}: {io_error}")))?;
            if entries.next().is_some() {
                return Err(usage_error(format!(
                    "{destination} is not empty; init never overwrites"
                )));
            }
            false
        }
        Err(_) => {
            std::fs::create_dir_all(destination.as_std_path())
                .map_err(|io_error| usage_error(format!("{destination}: {io_error}")))?;
            true
        }
    };

    // Everything below either completes or is removed again.
    let outcome = write_skeleton(destination, &files);
    if let Err(error) = outcome {
        if created_destination {
            let _ = std::fs::remove_dir_all(destination.as_std_path());
        } else {
            for (relative, _) in &files {
                let _ = std::fs::remove_file(destination.join(relative).as_std_path());
            }
            let _ = std::fs::remove_file(destination.join("lexlean.lock").as_std_path());
            let _ = std::fs::remove_dir_all(destination.join(".lexlean").as_std_path());
            let _ = std::fs::remove_dir(destination.join("src").as_std_path());
        }
        return Err(error);
    }
    Ok(())
}

fn write_skeleton(destination: &Utf8Path, files: &[(String, Vec<u8>)]) -> Result<(), LexLeanError> {
    for (relative, bytes) in files {
        let path = destination.join(relative);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent.as_std_path()).map_err(|io_error| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLV7010"),
                    format!("{relative}: {io_error}"),
                ))
            })?;
        }
        std::fs::write(path.as_std_path(), bytes).map_err(|io_error| {
            LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLV7010"),
                format!("{relative}: {io_error}"),
            ))
        })?;
    }
    // The canonical initial lock for builtin packages and workspace pins.
    let engine = Engine::load(&destination.join("lexlean.toml"))?;
    engine.lock(LockRequest {
        check_only: false,
        allow_network: false,
    })?;
    // The mutation lock file under the build root is not part of the
    // skeleton.
    let _ = std::fs::remove_dir_all(destination.join(".lexlean").as_std_path());
    Ok(())
}

/// The process entry point used by `main`: non-UTF-8 arguments or working
/// directory are the §8.3 environment diagnostic, never a panic.
#[must_use]
pub fn main_entry() -> i32 {
    let mut stdout = std::io::stdout();
    let mut stderr = std::io::stderr();
    let mut arguments: Vec<String> = Vec::new();
    let mut failure: Option<LexLeanError> = None;
    for argument in std::env::args_os() {
        match argument.into_string() {
            Ok(text) => arguments.push(text),
            Err(bad) => {
                if failure.is_none() {
                    failure = Some(LexLeanError::from_diagnostic(Diagnostic::new(
                        code!("LLV7008"),
                        format!(
                            "command-line argument {} is not valid UTF-8: {}",
                            arguments.len(),
                            bad.to_string_lossy()
                        ),
                    )));
                }
                arguments.push(bad.to_string_lossy().into_owned());
            }
        }
    }
    let working_directory = match std::env::current_dir() {
        Ok(directory) => match Utf8PathBuf::from_path_buf(directory) {
            Ok(utf8) => Some(utf8),
            Err(bad) => {
                if failure.is_none() {
                    failure = Some(LexLeanError::from_diagnostic(
                        crate::project::non_utf8_path(&bad),
                    ));
                }
                None
            }
        },
        Err(io_error) => {
            if failure.is_none() {
                failure = Some(LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLV7010"),
                    format!("the working directory is not available: {io_error}"),
                )));
            }
            None
        }
    };
    match (failure, working_directory) {
        (None, Some(directory)) => run(&arguments, &directory, &mut stdout, &mut stderr),
        (failure, _) => {
            let error = failure.unwrap_or_else(|| {
                LexLeanError::from_diagnostic(Diagnostic::new(
                    code!("LLV7010"),
                    "the working directory is not available",
                ))
            });
            // The mode and command are taken from the arguments that did
            // decode, so a JSON consumer still receives one object.
            emit(
                wants_json(&arguments),
                ColorMode::Auto,
                named_command(&arguments),
                &Outcome::default(),
                Err(error),
                &mut stdout,
                &mut stderr,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_capturing(arguments: &[&str]) -> (i32, String, String) {
        let arguments: Vec<String> = arguments.iter().map(|s| (*s).to_owned()).collect();
        let cwd = tempfile::tempdir().expect("tempdir");
        let cwd = Utf8Path::from_path(cwd.path()).expect("utf8").to_owned();
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let exit = run(&arguments, &cwd, &mut stdout, &mut stderr);
        (
            exit,
            String::from_utf8(stdout).expect("utf8"),
            String::from_utf8(stderr).expect("utf8"),
        )
    }

    #[test]
    fn usage_errors_keep_the_parser_lines_as_help() {
        // Human mode: the parser's first line is the LLC0001 message and
        // every further line is one help line, so the usage block keeps
        // its multi-line form instead of being flattened onto one line.
        let (exit, stdout, stderr) =
            run_capturing(&["lexlean", "--color", "never", "check", "--bogus"]);
        assert_eq!(exit, 2);
        assert!(stdout.is_empty(), "{stdout}");
        assert_eq!(
            stderr,
            "error[LLC0001]: unexpected argument '--bogus' found\n  help: tip: to pass '--bogus' as a value, use '-- --bogus'\n  help: Usage: lexlean check [OPTIONS] [INPUTS]...\n  help: For more information, try '--help'.\n"
        );
        // JSON mode carries the same lines structurally, stderr empty.
        let (exit, stdout, stderr) =
            run_capturing(&["lexlean", "--diagnostic-format", "json", "check", "--bogus"]);
        assert_eq!(exit, 2);
        assert!(stderr.is_empty(), "{stderr}");
        let value: serde_json::Value = serde_json::from_str(&stdout).expect("json");
        assert_eq!(value["diagnostics"][0]["code"], "LLC0001");
        assert_eq!(
            value["diagnostics"][0]["message"],
            "unexpected argument '--bogus' found"
        );
        assert_eq!(
            value["diagnostics"][0]["help"],
            serde_json::json!([
                "tip: to pass '--bogus' as a value, use '-- --bogus'",
                "Usage: lexlean check [OPTIONS] [INPUTS]...",
                "For more information, try '--help'."
            ])
        );
    }
}
