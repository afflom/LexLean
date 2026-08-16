//! Scoped identifiers (SPEC.md §14.2): section parameters, declaration
//! binders, proof locals and hypotheses, and branch binders, with
//! capture-free `LocalId` identity (I9).

use crate::ir::term::{LocalId, Term};

/// Monotone allocation of project-unique local identities.
#[derive(Debug, Default)]
pub struct LocalAlloc {
    next: u64,
}

impl LocalAlloc {
    /// The next fresh identity.
    pub fn fresh(&mut self) -> LocalId {
        let id = LocalId(self.next);
        self.next += 1;
        id
    }
}

/// One scoped declaration.
#[derive(Debug, Clone)]
pub struct ScopeEntry {
    /// The display spelling.
    pub spelling: String,
    /// The identity.
    pub id: LocalId,
    /// The conservatively known type; `None` where the type is not
    /// statically known (branch binders, post-rewrite hypotheses).
    pub ty: Option<Term>,
}

/// The lexical scope stack. Inner locals shadow an identically spelled
/// outer local; local identifiers never shadow text glossary forms (§14.2),
/// which holds structurally because glossary resolution consults the
/// closure, not this stack.
#[derive(Debug, Default)]
pub struct ScopeStack {
    frames: Vec<Vec<ScopeEntry>>,
}

impl ScopeStack {
    /// Enter a scope frame.
    pub fn push_frame(&mut self) {
        self.frames.push(Vec::new());
    }

    /// Leave the innermost frame.
    pub fn pop_frame(&mut self) {
        self.frames.pop();
    }

    /// Declare a local in the innermost frame.
    pub fn declare(&mut self, spelling: &str, id: LocalId, ty: Option<Term>) {
        if let Some(frame) = self.frames.last_mut() {
            frame.push(ScopeEntry {
                spelling: spelling.to_owned(),
                id,
                ty,
            });
        }
    }

    /// Resolve a spelling, innermost first.
    #[must_use]
    pub fn lookup(&self, spelling: &str) -> Option<&ScopeEntry> {
        self.frames
            .iter()
            .rev()
            .find_map(|frame| frame.iter().rev().find(|entry| entry.spelling == spelling))
    }

    /// Is the spelling unused anywhere in scope? Freshness for `Assume`,
    /// `have`, and branch binders (§16.2, §16.3).
    #[must_use]
    pub fn is_fresh(&self, spelling: &str) -> bool {
        self.lookup(spelling).is_none()
    }

    /// Forget the conservatively known type of one local (after a rewrite
    /// or simplify at that hypothesis).
    pub fn forget_type(&mut self, id: LocalId) {
        for frame in &mut self.frames {
            for entry in frame.iter_mut() {
                if entry.id == id {
                    entry.ty = None;
                }
            }
        }
    }

    /// Every entry, outermost first, for use-analysis.
    #[must_use]
    pub fn entries(&self) -> Vec<&ScopeEntry> {
        self.frames.iter().flatten().collect()
    }
}
