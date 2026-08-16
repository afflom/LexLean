//! The command-line interface (SPEC.md §23): exact commands, exact exit
//! codes, and the two diagnostic output modes. No environment variable
//! changes semantic configuration (CL-17).

use std::collections::BTreeSet;
use std::io::Write;

use camino::{Utf8Path, Utf8PathBuf};
use clap::{Parser, Subcommand, ValueEnum};

use crate::api::{
    command_result_json, BuildRequest, CheckRequest, Engine, FormatRequest, LockRequest, Selection,
    VerifyRequest,
};
use crate::code;
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

/// The embedded diagnostic registry, for `explain` (§23.4). The registry
/// file is the single source (R1); the binary carries a copy.
const ERRORS_TOML: &str = include_str!(concat!(env!("OUT_DIR"), "/errors.toml"));

fn selection_from(all: bool, inputs: Vec<Utf8PathBuf>) -> Result<Selection, LexLeanError> {
    match (all, inputs.is_empty()) {
        (true, true) => Ok(Selection::All),
        (true, false) => Err(LexLeanError::from_diagnostic(Diagnostic::new(
            code!("LLC0002"),
            "--all and explicit inputs are mutually exclusive",
        ))),
        (false, true) => Ok(Selection::Entrypoints),
        (false, false) => Ok(Selection::Files(inputs.into_iter().collect())),
    }
}

fn print_human_diagnostics(stderr: &mut dyn Write, error: &LexLeanError, max: usize) {
    for diagnostic in error.diagnostics.iter().take(max) {
        let _ = write!(
            stderr,
            "error[{}]: {}",
            diagnostic.code.as_str(),
            diagnostic.message
        );
        if let Some(span) = &diagnostic.primary {
            let _ = write!(
                stderr,
                "\n  --> {}:{}:{}",
                span.path, span.line_start, span.column_start
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
    if error.diagnostics.len() > max {
        let _ = writeln!(
            stderr,
            "  ... and {} more diagnostics (max_diagnostics)",
            error.diagnostics.len() - max
        );
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

fn explain_text(requested: &str) -> Option<String> {
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

/// Run the CLI against explicit argument and output streams; returns the
/// exact documented exit code (§23.6).
#[allow(clippy::too_many_lines)]
pub fn run(
    arguments: &[String],
    working_directory: &Utf8Path,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> i32 {
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
            let _ = write!(stderr, "{clap_error}");
            return 2;
        }
    };
    if parsed.version {
        let _ = write!(stdout, "{}", version_text());
        return 0;
    }
    let Some(command) = parsed.command else {
        let _ = writeln!(stderr, "error[LLC0001]: a command is required; see --help");
        return 2;
    };
    let json_mode = parsed.diagnostic_format == DiagnosticFormat::Json;
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

    let mut modules: BTreeSet<String> = BTreeSet::new();
    let mut artifacts: Vec<String> = Vec::new();
    let mut summary = String::new();
    let outcome: Result<(), LexLeanError> = (|| match command {
        CommandKind::Explain { code: requested } => match explain_text(&requested) {
            Some(text) => {
                summary = text;
                Ok(())
            }
            None => Err(LexLeanError::from_diagnostic(Diagnostic::new(
                code!("LLC0001"),
                format!("`{requested}` is not a registered diagnostic code"),
            ))),
        },
        CommandKind::Init {
            path,
            name,
            module_prefix,
        } => {
            let destination = match path {
                Some(given) if given.is_relative() => working_directory.join(given),
                Some(given) => given,
                None => working_directory.to_path_buf(),
            };
            init_project(&destination, &name, &module_prefix)?;
            summary = format!("initialized {destination}\n");
            Ok(())
        }
        other => {
            let config_path = match &parsed.project {
                Some(explicit) => explicit.clone(),
                None => crate::project::discover(working_directory)?,
            };
            let engine = Engine::load(&config_path)?;
            let max_diagnostics = engine.project().config.limits.max_diagnostics;
            let _ = max_diagnostics;
            match other {
                CommandKind::Lock {
                    check,
                    allow_network,
                } => {
                    let result = engine.lock(LockRequest {
                        check_only: check,
                        allow_network,
                    })?;
                    summary = if result.written {
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
                    modules = result.units.keys().cloned().collect();
                    summary = format!(
                        "checked {} modules (source {}, semantic {})\n",
                        result.units.len(),
                        result.source_id.to_hex(),
                        result.semantic_id.to_hex()
                    );
                    Ok(())
                }
                CommandKind::Build { all, inputs } => {
                    let result = engine.build(BuildRequest {
                        selection: selection_from(all, inputs)?,
                    })?;
                    modules = result.units.keys().cloned().collect();
                    if let Some(id) = result.build_id {
                        artifacts.push(format!(
                            "{}/build/{}",
                            engine.project().config.build_root,
                            id.to_hex()
                        ));
                        summary = format!(
                            "built {} modules at {}\n",
                            result.units.len(),
                            artifacts.last().expect("just pushed")
                        );
                    }
                    Ok(())
                }
                CommandKind::Verify { all, inputs } => {
                    let result = engine.verify(VerifyRequest {
                        selection: selection_from(all, inputs)?,
                    })?;
                    modules = result.units.keys().cloned().collect();
                    artifacts.push(format!(
                        "{}/verified/{}",
                        engine.project().config.build_root,
                        result.attestation_id.to_hex()
                    ));
                    summary = format!(
                        "verified {} modules; attestation {}\n",
                        result.units.len(),
                        result.attestation_id.to_hex()
                    );
                    Ok(())
                }
                CommandKind::Fmt { check, all, inputs } => {
                    let result = engine.format(FormatRequest {
                        selection: selection_from(all, inputs)?,
                        check_only: check,
                    })?;
                    modules = result.units.keys().cloned().collect();
                    let rewritten = result.units.values().filter(|already| !**already).count();
                    summary = if check {
                        format!("{} modules are canonical\n", result.units.len())
                    } else {
                        format!("formatted {rewritten} modules\n")
                    };
                    Ok(())
                }
                CommandKind::Clean => {
                    engine.clean()?;
                    summary = format!("removed {}\n", engine.project().config.build_root);
                    Ok(())
                }
                CommandKind::Init { .. } | CommandKind::Explain { .. } => {
                    unreachable!("handled above")
                }
            }
        }
    })();

    let (exit_code, error) = match outcome {
        Ok(()) => (0, None),
        Err(error) => (error.class.exit_code(), Some(error)),
    };
    if json_mode {
        let empty = Vec::new();
        let diagnostics = error.as_ref().map_or(&empty, |e| &e.diagnostics);
        let json = command_result_json(command_name, exit_code, &modules, &artifacts, diagnostics);
        let _ = stdout.write_all(&json.to_file_bytes());
    } else {
        if exit_code == 0 && !summary.is_empty() {
            let _ = write!(stdout, "{summary}");
        }
        if let Some(error) = &error {
            print_human_diagnostics(stderr, error, 256);
        }
    }
    exit_code
}

/// Create a new project skeleton (§23.4): only in an absent or empty
/// directory, never overwriting.
fn init_project(
    destination: &Utf8Path,
    name: &str,
    module_prefix: &str,
) -> Result<(), LexLeanError> {
    let config_error =
        |message: String| LexLeanError::from_diagnostic(Diagnostic::new(code!("LLC0001"), message));
    if destination.as_std_path().exists() {
        let mut entries = std::fs::read_dir(destination.as_std_path())
            .map_err(|io_error| config_error(format!("{destination}: {io_error}")))?;
        if entries.next().is_some() {
            return Err(config_error(format!(
                "{destination} is not empty; init never overwrites"
            )));
        }
    } else {
        std::fs::create_dir_all(destination.as_std_path())
            .map_err(|io_error| config_error(format!("{destination}: {io_error}")))?;
    }
    let write = |relative: &str, bytes: &[u8]| -> Result<(), LexLeanError> {
        let path = destination.join(relative);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent.as_std_path())
                .map_err(|io_error| config_error(format!("{path}: {io_error}")))?;
        }
        std::fs::write(path.as_std_path(), bytes)
            .map_err(|io_error| config_error(format!("{path}: {io_error}")))
    };
    let host_lib = format!("{}Host", module_prefix.replace('.', ""));
    let lake_name = name.replace('-', "_");
    write(
        "lexlean.toml",
        format!(
            "spec = \"lexlean/project/1\"\nname = \"{name}\"\nlanguage = \"1.0\"\nmodule_prefix = \"{module_prefix}\"\nsource_roots = [\"src\"]\nentrypoints = [\"src/Main.lex.tex\"]\nbuild_root = \".lexlean\"\nlockfile = \"lexlean.lock\"\nlean_workspace = \".\"\nlean_toolchain = \"{}\"\n\n[[lexicon_source]]\npackage = \"lexlean.std.nat\"\nkind = \"builtin\"\n\n[limits]\nmax_file_bytes = 4194304\nmax_total_source_bytes = 67108864\nmax_primitive_atoms = 2000000\nmax_token_lattice_edges = 4000000\nmax_parse_states = 4000000\nmax_ir_nodes = 2000000\nmax_scope_depth = 1024\nmax_import_depth = 128\nmax_diagnostics = 256\nmax_child_output_bytes = 16777216\nchild_timeout_ms = 300000\n",
            crate::LEAN_TOOLCHAIN
        )
        .as_bytes(),
    )?;
    write(
        "lean-toolchain",
        format!("{}\n", crate::LEAN_TOOLCHAIN).as_bytes(),
    )?;
    write(
        "lakefile.toml",
        format!(
            "name = \"{lake_name}_host\"\nversion = \"0.1.0\"\ndefaultTargets = [\"{host_lib}\"]\n\n[[lean_lib]]\nname = \"{host_lib}\"\n"
        )
        .as_bytes(),
    )?;
    write(&format!("{host_lib}.lean"), b"module\nimport Init\n")?;
    write(
        "src/Main.lex.tex",
        b"\\begin{lexlean}{Main}\n\\useglossary{lexlean.std.nat@1.0.0}\n\\title{addition}\n\\end{lexlean}\n",
    )?;
    write(".gitignore", b"/.lexlean/\n")?;
    // The canonical initial lock for builtin packages and workspace pins.
    let engine = Engine::load(&destination.join("lexlean.toml"))?;
    engine.lock(LockRequest {
        check_only: false,
        allow_network: false,
    })?;
    Ok(())
}

/// The process entry point used by `main`.
#[must_use]
pub fn main_entry() -> i32 {
    let arguments: Vec<String> = std::env::args().collect();
    let working_directory = std::env::current_dir()
        .ok()
        .and_then(|directory| Utf8PathBuf::from_path_buf(directory).ok())
        .unwrap_or_else(|| Utf8PathBuf::from("."));
    let mut stdout = std::io::stdout();
    let mut stderr = std::io::stderr();
    run(&arguments, &working_directory, &mut stdout, &mut stderr)
}
