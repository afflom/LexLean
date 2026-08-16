//! The conformance case registry (SPEC.md §27.8, §31).
//!
//! Every generated test `conformance_<id>` calls [`run`] with its ID; the
//! dispatch panics for an unwired ID, so a registered capability cannot
//! pass before its case exists.

mod artifacts;
mod cli_api;
mod configuration_lock;
mod declarations;
mod examples;
mod grammar;
mod latex_pdf;
mod lean_backend;
mod lexical_closure;
mod lexicon;
mod proofs;
mod repository;
mod security;
mod semantic_ir;
mod verification;

/// Run the case for one conformance ID.
///
/// # Panics
///
/// Panics when the case's assertion fails, and for an ID with no wired
/// case — an unimplemented registered capability must not pass silently.
pub fn run(id: &str) {
    let prefix = id.split('-').next().unwrap_or_default();
    match prefix {
        "RP" => repository::run(id),
        "CF" => configuration_lock::run(id),
        "LX" => lexical_closure::run(id),
        "GL" => lexicon::run(id),
        "GR" => grammar::run(id),
        "SM" => semantic_ir::run(id),
        "DF" => declarations::run(id),
        "PF" => proofs::run(id),
        "LN" => lean_backend::run(id),
        "TX" => latex_pdf::run(id),
        "AR" => artifacts::run(id),
        "VR" => verification::run(id),
        "CL" => cli_api::run(id),
        "SE" => security::run(id),
        "EX" => examples::run(id),
        _ => panic!("no conformance case is wired for {id}"),
    }
}
