-- The standing axiom gate for the vendored Atlas library (release plan section 4.4).
--
-- This is a gate, not a measurement: it enumerates *every* declaration the library
-- exports and fails on any axiom outside Lean's own three. Enumerating rather than
-- listing names is the point --- a hand-written list of `#print axioms` lines
-- silently stops covering a declaration the moment someone adds one.
--
-- It lives outside the library's own `lean_lib` because it imports `Lean` for the
-- environment walk, and the library itself is prelude-only.

import Lean
import UorAtlas

open Lean

/-- The only axioms a declaration in this library may depend on: Lean's own. -/
def permitted : List Name := [``propext, ``Quot.sound, ``Classical.choice]

def auditAxioms : CoreM Unit := do
  let env ← getEnv
  let mut checked := 0
  let mut offences : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    unless (`UorAtlas).isPrefixOf name do continue
    if name.isInternal || name.isImplementationDetail then continue
    checked := checked + 1
    for ax in (← collectAxioms name) do
      unless permitted.contains ax do
        offences := offences.push (name, ax)
  -- A gate that inspected nothing has not passed. If the prefix filter ever
  -- stops matching --- a namespace rename, a root module that no longer pulls
  -- the library in, an `import` dropped from this file --- every `continue`
  -- above fires, `offences` stays empty, and the audit would report success
  -- over zero declarations. The floor is deliberately far below the real count
  -- so it never needs updating, and far above zero so it cannot be satisfied
  -- by an empty environment.
  if checked < 100 then
    throwError s!"atlas-library-axioms: only {checked} declaration(s) were inspected; the library is not in this environment and the audit has checked nothing"
  if offences.isEmpty then
    IO.println s!"atlas-library-axioms: {checked} declarations, none depends on an axiom outside Lean's three"
  else
    for (n, a) in offences do
      IO.println s!"atlas-library-axioms: `{n}` depends on `{a}`"
    throwError s!"atlas-library-axioms: {offences.size} declaration(s) depend on an unpermitted axiom"

#eval auditAxioms
