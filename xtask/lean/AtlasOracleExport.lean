/-
The migration oracle for the native Atlas source.  This program reads the
elaborated environment rather than the spelling of the old modules: types,
values, universe parameters, inductive metadata, and dependency edges are the
semantic objects that the LexLean importer consumes.
-/

import Lean
import Lean.Meta.Instances
import Lean.OriginalConstKind
import UorAtlas

open Lean

namespace LexLean.AtlasOracle

private def moduleOf? (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  env.header.moduleNames[index.toNat]?

private def isAtlasModule (name : Name) : Bool :=
  (`UorAtlas).isPrefixOf name

private def isAtlasDeclaration (env : Environment) (name : Name) : Bool :=
  (moduleOf? env name).any isAtlasModule

private def infoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo value => if value.hints.isAbbrev then "abbrev" else "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def value? : ConstantInfo → Option Expr
  | .defnInfo value => some value.value
  | .thmInfo value => some value.value
  | .opaqueInfo value => some value.value
  | _ => none

private def reducibilityJson? : ConstantInfo → Option Json
  | .defnInfo value =>
      some <| match value.hints with
      | .abbrev => Json.mkObj [("kind", "abbrev")]
      | .opaque => Json.mkObj [("kind", "opaque")]
      | .regular height => Json.mkObj [("kind", "regular"), ("height", height.toNat)]
  | _ => none

private def binderInfo : BinderInfo → String
  | .default => "e"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

private partial def levelJson : Level → Json
  | .zero => Json.mkObj [("k", "z")]
  | .succ inner => Json.mkObj [("k", "s"), ("a", levelJson inner)]
  | .max left right =>
      Json.mkObj [("k", "m"), ("a", Json.arr #[levelJson left, levelJson right])]
  | .imax left right =>
      Json.mkObj [("k", "i"), ("a", Json.arr #[levelJson left, levelJson right])]
  | .param name => Json.mkObj [("k", "p"), ("a", name.toString)]
  | .mvar _ => panic! "closed Atlas declaration contains a universe metavariable"

private def safeSegment (segment : String) : Bool :=
  match segment.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha || first == '_') &&
        rest.all fun char => char.isAlphanum || char == '_' || char == '?' || char == '\''

private def safeName (name : Name) : Bool :=
  name.toString.splitOn "." |>.all safeSegment

private def renamedNames (declarations : Array (Name × ConstantInfo)) : Std.HashMap Name Name :=
  Id.run do
    let mut names : Std.HashMap Name Name := {}
    let mut next := 0
    for (name, _) in declarations do
      if isPrivateName name || name.isInternal || name.isImplementationDetail || !safeName name then
        let baseName := `UorAtlas.LexLeanInternal
        names := names.insert name (baseName.str s!"decl{next}")
        next := next + 1
      else
        names := names.insert name name
    return names

private def exportedName (names : Std.HashMap Name Name) (name : Name) : Name :=
  names.getD name name

private structure DagState where
  ids : Std.HashMap (Expr × Nat) Nat := {}
  nodes : Array Json := #[]
  expressions : Array Expr := #[]

private partial def intern (env : Environment) (names : Std.HashMap Name Name)
    (expression : Expr) (depth : Nat := 0) : StateM DagState Nat := do
  if let .mdata _ body := expression then
    return ← intern env names body depth
  -- A raw de Bruijn expression only has meaning at its traversal depth.
  -- Closed terms remain globally shareable; open terms are interned per scope.
  let key := (expression, if expression.hasLooseBVars then depth else 0)
  if let some id := (← get).ids.get? key then
    return id
  let json ← match expression with
    | .bvar index => pure <| Json.mkObj [("k", "b"), ("i", index)]
    | .fvar _ => panic! "closed Atlas declaration contains a free variable"
    | .mvar _ => panic! "closed Atlas declaration contains a metavariable"
    | .sort level => pure <| Json.mkObj [("k", "s"), ("l", levelJson level)]
    | .const name levels =>
        if isAtlasDeclaration env name then
          pure <| Json.mkObj [
            ("k", "c"),
            ("n", (exportedName names name).toString),
            ("u", Json.arr <| levels.toArray.map levelJson)]
        else if safeName name then
          pure <| Json.mkObj [
            ("k", "c"), ("n", name.toString),
            ("u", Json.arr <| levels.toArray.map levelJson)]
        else
          panic! s!"Atlas expression references inaccessible external name `{name}`"
    | .app function argument =>
        let function ← intern env names function depth
        let argument ← intern env names argument depth
        pure <| Json.mkObj [("k", "a"), ("f", function), ("x", argument)]
    | .lam _ type body info =>
        let type ← intern env names type depth
        let body ← intern env names body (depth + 1)
        pure <| Json.mkObj [
          ("k", "l"), ("n", ""), ("b", binderInfo info),
          ("t", type), ("v", body)]
    | .forallE _ type body info =>
        let type ← intern env names type depth
        let body ← intern env names body (depth + 1)
        pure <| Json.mkObj [
          ("k", "p"), ("n", ""), ("b", binderInfo info),
          ("t", type), ("v", body)]
    | .letE _ type value body nondep =>
        let type ← intern env names type depth
        let value ← intern env names value depth
        let body ← intern env names body (depth + 1)
        pure <| Json.mkObj [
          ("k", "e"), ("n", ""), ("t", type), ("v", value),
          ("body", body), ("d", nondep)]
    | .lit (.natVal value) =>
        pure <| Json.mkObj [("k", "n"), ("v", toString value)]
    | .lit (.strVal value) =>
        pure <| Json.mkObj [
          ("k", "t"),
          ("v", Json.arr <| value.toList.toArray.map fun char => toJson char.toNat)]
    | .mdata _ _ => unreachable!
    | .proj typeName index value =>
        let some info := getStructureInfo? env typeName
          | panic! s!"projection expression names unregistered structure `{typeName}`"
        let some projection := info.getProjFn? index
          | panic! s!"projection {index} is absent from `{typeName}`"
        let value ← intern env names value depth
        pure <| Json.mkObj [
          ("k", "j"),
          ("n", (exportedName names projection).toString),
          ("s", (exportedName names typeName).toString),
          ("i", index),
          ("x", value)]
  let mut state ← get
  let id := state.nodes.size
  state := { state with
    ids := state.ids.insert key id
    nodes := state.nodes.push json
    expressions := state.expressions.push expression }
  set state
  return id

private def declarationJson (env : Environment) (names : Std.HashMap Name Name)
    (name : Name) (info : ConstantInfo) : StateM DagState Json := do
  let type ← intern env names info.type
  let value ← (value? info).mapM (intern env names)
  let structureInfo := getStructureInfo? env name
  let inductiveJson ← match info with
    | .inductInfo metadata =>
        let projections := structureInfo.map (fun structureData =>
          structureData.fieldNames.filterMap fun field =>
            structureData.fieldInfo.find? (fun row => row.fieldName == field) |>.map fun row =>
              (exportedName names row.projFn).toString) |>.getD #[]
        pure <| some <| Json.mkObj [
          ("num_params", metadata.numParams),
          ("num_indices", metadata.numIndices),
          ("constructors", Json.arr <| metadata.ctors.toArray.map fun ctor =>
            toJson (exportedName names ctor).toString),
          ("structure", structureInfo.isSome),
          ("projections", Json.arr <| projections.map toJson)]
    | _ => pure none
  let generated := match info with
    | .ctorInfo metadata => some metadata.induct
    | .recInfo metadata => metadata.all.head?
    | _ =>
        if name.toString.endsWith "._unsafe_rec" then
          some name
        else none
  let isInstance := Meta.isInstanceCore env name
  let priority :=
    if isInstance then
      Meta.instanceExtension.getState env |>.instanceNames.find? name |>.map (·.priority)
    else
      none
  let mut fields : List (String × Json) := [
    ("name", (exportedName names name).toString),
    ("levels", Json.arr <| info.levelParams.toArray.map fun level => toJson level.toString),
    ("kind", infoKind info),
    ("policy", Json.mkObj [
      ("kind", "allow"),
      ("axioms", Json.arr #["Classical.choice", "Quot.sound", "propext"])]),
    ("type", type),
    ("class", isClass env name),
    ("instance", isInstance),
    ("generated", generated.isSome)]
  if let some value := value then fields := ("value", value) :: fields
  if let some reducibility := reducibilityJson? info then
    fields := ("reducibility", reducibility) :: fields
  if let some inductiveData := inductiveJson then fields := ("inductive", inductiveData) :: fields
  if let some priority := priority then fields := ("priority", priority) :: fields
  return Json.mkObj fields

def writeSource (path : System.FilePath) : CoreM Unit := do
  let env ← getEnv
  let mut declarations : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if isAtlasDeclaration env name then declarations := declarations.push (name, info)
  declarations := declarations.qsort fun left right => Name.quickLt left.1 right.1
  let names := renamedNames declarations
  let mut state : DagState := {}
  let mut rows : Array Json := #[]
  for (name, info) in declarations do
    let (row, next) := (declarationJson env names name info).run state
    state := next
    rows := rows.push row
  let proofNodes ← Meta.MetaM.run' do
    let mut nodes : Array Json := #[]
    for index in [:state.expressions.size] do
      let expression := state.expressions[index]!
      if !expression.hasLooseBVars then
        try
          if ← Meta.isProof expression then
            nodes := nodes.push (toJson index)
        catch _ => pure ()
    return nodes
  let payload := Json.mkObj [
    ("spec", "lexlean/core-module/1"),
    ("imports", Json.arr #["Init"]),
    ("nodes", Json.arr state.nodes),
    ("proof_nodes", Json.arr proofNodes),
    ("declarations", Json.arr rows)] |>.compress
  let source := "\\begin{lexlean}{Atlas}\n\\title{Atlas definition one label}\n\\begin{coremodule}\n\\coredata{" ++
    payload ++ "}\n\\end{coremodule}\n\\end{lexlean}\n"
  IO.FS.writeFile path source
  IO.println s!"atlas-oracle-export: {declarations.size} declarations, {state.nodes.size} shared nodes, {source.utf8ByteSize} bytes"

def audit : CoreM Unit := do
  let env ← getEnv
  let mut declarations : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if isAtlasDeclaration env name then
      declarations := declarations.push (name, info)
  declarations := declarations.qsort fun left right => Name.quickLt left.1 right.1

  let mut kinds : Std.HashMap String Nat := {}
  let mut structures := 0
  let mut classes := 0
  let mut instances := 0
  let mut internals := 0
  let mut expressionsWithFreeVariables := 0
  let mut expressionsWithMetavariables := 0
  let mut atlasDependencies : Std.HashSet Name := {}
  let mut unsafeDeclarations := 0
  let mut recursiveValues := 0
  for (name, info) in declarations do
    let kind := infoKind info
    kinds := kinds.insert kind (kinds.getD kind 0 + 1)
    if (getStructureInfo? env name).isSome then structures := structures + 1
    if isClass env name then classes := classes + 1
    if Meta.isInstanceCore env name then instances := instances + 1
    if name.isInternal || name.isImplementationDetail then internals := internals + 1
    if info.isUnsafe then unsafeDeclarations := unsafeDeclarations + 1
    if let some value := value? info then
      let selfReference := value.foldConsts false fun dependency found => found || dependency == name
      if selfReference then
        recursiveValues := recursiveValues + 1
    for expression in #[info.type] ++ (value? info).toArray do
      if expression.hasFVar then
        expressionsWithFreeVariables := expressionsWithFreeVariables + 1
      if expression.hasMVar then
        expressionsWithMetavariables := expressionsWithMetavariables + 1
      atlasDependencies := expression.foldConsts atlasDependencies fun dependency found =>
        if isAtlasDeclaration env dependency then found.insert dependency else found

  IO.println s!"atlas-oracle: declarations={declarations.size} structures={structures} classes={classes} instances={instances} internal={internals}"
  let mut kindRows := kinds.toList.toArray
  kindRows := kindRows.qsort fun left right => left.1 < right.1
  for (kind, count) in kindRows do
    IO.println s!"atlas-oracle-kind: {kind}={count}"
  IO.println s!"atlas-oracle-expressions: expressions-with-fvars={expressionsWithFreeVariables} expressions-with-mvars={expressionsWithMetavariables} atlas-dependencies={atlasDependencies.size}"
  IO.println s!"atlas-oracle-safety: unsafe={unsafeDeclarations} recursive-values={recursiveValues}"
  if declarations.isEmpty then
    throwError "Atlas oracle found no declarations"
  if expressionsWithFreeVariables != 0 || expressionsWithMetavariables != 0 then
    throwError s!"Atlas oracle contains {expressionsWithFreeVariables} expression(s) with free variables and {expressionsWithMetavariables} expression(s) with metavariables"

end LexLean.AtlasOracle

#eval LexLean.AtlasOracle.audit

def LexLean.AtlasOracle.writeIfRequested : CoreM Unit := do
  if let some path ← IO.getEnv "LEXLEAN_ATLAS_EXPORT" then
    writeSource path

#eval LexLean.AtlasOracle.writeIfRequested
