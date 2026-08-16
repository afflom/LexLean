//! LexLean: a closed-lexicon LaTeX-to-Lean 4 compiler whose canonical
//! document and prose-free Lean program are generated from one semantic
//! representation.
//!
//! The complete implementation contract is `SPEC.md` at the repository root;
//! nothing here is normative beyond what it authorizes. The stable public
//! surface is [`Engine`] with its request and result types (SPEC.md §24);
//! the full mutable compiler IR stays internal.

#![forbid(unsafe_code)]

pub mod api;
pub mod artifact;
pub mod backend;
pub mod cli;
pub mod config;
pub mod diagnostic;
pub mod elaborate;
pub mod error;
pub mod fmt;
pub mod grammar;
pub mod ir;
pub mod lexicon;
pub mod link;
pub mod lock;
pub mod project;
pub mod source;
pub mod verify;

pub use api::{
    BuildRequest, BuiltUnit, CheckRequest, CheckedUnit, CheckedUnitSummary, Engine, FormatRequest,
    FormatResultSet, LockRequest, LockResult, ModuleArtifacts, ProjectResultSet, Selection,
    VerifiedProject, VerifiedUnit, VerifyRequest,
};
pub use error::{ErrorClass, LexLeanError};

use artifact::content_id::{tree_digest, Sha256Digest};

/// The embedded normative data: `language/`, `schemas/`, and the committed
/// axiom-parser and canonical-JSON golden fixtures (SPEC.md §21.2).
pub mod embedded {
    include!(concat!(env!("OUT_DIR"), "/embedded.rs"));
}

/// The language identifier accepted by this compiler (SPEC.md §10.1).
pub const LANGUAGE_VERSION: &str = "1.0";

/// The exact pinned Lean toolchain string (SPEC.md §8.2).
pub const LEAN_TOOLCHAIN: &str = "leanprover/lean4:v4.32.1";

/// The Lean version a verification environment must report (SPEC.md §8.2).
pub const LEAN_VERSION: &str = "4.32.1";

/// The compiler crate version.
pub const COMPILER_VERSION: &str = env!("CARGO_PKG_VERSION");

/// The compiler-semantics ID: the §11.5 tree digest of every embedded
/// normative file, computed once per process (SPEC.md §21.2). Repository
/// tests recompute the same digest from disk and compare (RP-10).
#[must_use]
pub fn compiler_semantics_id() -> Sha256Digest {
    use std::sync::OnceLock;
    static ID: OnceLock<Sha256Digest> = OnceLock::new();
    *ID.get_or_init(|| tree_digest(embedded::FILES))
}
