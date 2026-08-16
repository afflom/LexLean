//! The linked semantic IR (SPEC.md §17): closed term, proof, declaration,
//! and document representations. No variant is open-ended; there is no
//! opaque prose node (I4, I6).

pub mod declaration;
pub mod document;
pub mod proof;
pub mod term;
