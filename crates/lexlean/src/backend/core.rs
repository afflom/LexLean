//! Rendering of the closed kernel-term module IR.  Both outputs walk the
//! same node DAG; neither accepts a source-language or backend-text payload.

use std::collections::{BTreeMap, BTreeSet};

use crate::artifact::source_map::MapRole;
use crate::backend::{EmitSource, Emitter};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::core::{
    CoreBinderInfo, CoreDeclKind, CoreDeclaration, CoreLevel, CoreModule, CoreNode,
};
use crate::link::CheckedModule;
use crate::source::coverage::Origin;

fn internal(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(
        code!("LLI9001"),
        format!("phase core backend: {}", message.into()),
    )
}

fn source_range(checked: &CheckedModule) -> (usize, usize) {
    let mut start = usize::MAX;
    let mut end = 0;
    for row in &checked.coverage_source {
        if matches!(&row.binding, Origin::Metadata { owner } if owner == "lexlean.core::coredata") {
            start = start.min(row.byte_start);
            end = end.max(row.byte_end);
        }
    }
    if start == usize::MAX {
        (0, checked.normalized.len())
    } else {
        (start, end)
    }
}

fn emit_chunk(emitter: &mut Emitter, checked: &CheckedModule, node: usize, text: &str, kind: &str) {
    let (start, end) = source_range(checked);
    emitter.piece(
        text,
        kind,
        Origin::Metadata {
            owner: "lexlean.core::coredata".to_owned(),
        },
        EmitSource::File(start, end),
        MapRole::Declaration,
        node,
    );
}

struct Printer<'a> {
    module: &'a CoreModule,
    helpers: &'a BTreeSet<usize>,
    shared_open: &'a BTreeSet<usize>,
    requirements: &'a [usize],
}

impl Printer<'_> {
    fn level(level: &CoreLevel) -> String {
        match level {
            CoreLevel::Zero => "0".to_owned(),
            CoreLevel::Succ(inner) => format!("({} + 1)", Self::level(inner)),
            CoreLevel::Max(pair) => {
                format!("(max {} {})", Self::level(&pair.0), Self::level(&pair.1))
            }
            CoreLevel::IMax(pair) => {
                format!("(imax {} {})", Self::level(&pair.0), Self::level(&pair.1))
            }
            CoreLevel::Param(name) => name.clone(),
        }
    }

    fn universes(levels: &[CoreLevel]) -> String {
        if levels.is_empty() {
            String::new()
        } else {
            format!(
                ".{{{}}}",
                levels
                    .iter()
                    .map(Self::level)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    }

    fn binder_name(depth: usize) -> String {
        format!("llc{depth}")
    }

    fn binder(info: CoreBinderInfo, name: &str, ty: &str) -> String {
        match info {
            CoreBinderInfo::Explicit => format!("({name} : {ty})"),
            CoreBinderInfo::Implicit => format!("{{{name} : {ty}}}"),
            CoreBinderInfo::StrictImplicit => format!("{{strict {name} : {ty}}}"),
            CoreBinderInfo::Instance => format!("[{name} : {ty}]"),
        }
    }

    fn term(&self, root: usize, scope: &mut Vec<String>) -> Result<String, Diagnostic> {
        self.walk(root, scope, None, &BTreeMap::new())
    }

    fn walk(
        &self,
        root: usize,
        scope: &mut Vec<String>,
        expanding_helper: Option<usize>,
        locals: &BTreeMap<usize, String>,
    ) -> Result<String, Diagnostic> {
        if let Some(name) = locals.get(&root) {
            return Ok(name.clone());
        }
        if self.helpers.contains(&root) && expanding_helper != Some(root) {
            return Ok(self.helper_reference(root));
        }
        let node = self
            .module
            .nodes
            .get(root)
            .ok_or_else(|| internal(format!("absent expression node {root}")))?;
        Ok(match node {
            CoreNode::BVar { i } => scope
                .len()
                .checked_sub(i + 1)
                .and_then(|index| scope.get(index))
                .cloned()
                .ok_or_else(|| internal(format!("loose de Bruijn index {i} at node {root}")))?,
            CoreNode::Sort { l } => format!("(Sort {})", Self::level(l)),
            CoreNode::Const { n, u } => format!("{n}{}", Self::universes(u)),
            CoreNode::App { .. } => {
                let mut arguments = Vec::new();
                let mut head = root;
                while let CoreNode::App { f, x } = self
                    .module
                    .nodes
                    .get(head)
                    .ok_or_else(|| internal(format!("absent application node {head}")))?
                {
                    arguments.push(*x);
                    head = *f;
                }
                arguments.reverse();
                let mut text = String::from("(");
                text.push_str(&self.application_head(head, scope, expanding_helper, locals)?);
                for argument in arguments {
                    text.push(' ');
                    text.push_str(&self.walk(argument, scope, expanding_helper, locals)?);
                }
                text.push(')');
                text
            }
            CoreNode::Lambda { b, t, v, .. } => {
                let ty = self.walk(*t, scope, expanding_helper, locals)?;
                let name = Self::binder_name(scope.len());
                scope.push(name.clone());
                let value = self.binder_body(*v, scope, expanding_helper, locals)?;
                scope.pop();
                format!("(fun {} => {value})", Self::binder(*b, &name, &ty))
            }
            CoreNode::Forall { b, t, v, .. } => {
                let ty = self.walk(*t, scope, expanding_helper, locals)?;
                let name = Self::binder_name(scope.len());
                scope.push(name.clone());
                let value = self.binder_body(*v, scope, expanding_helper, locals)?;
                scope.pop();
                format!("({} -> {value})", Self::binder(*b, &name, &ty))
            }
            CoreNode::Let { t, v, body, .. } => {
                let ty = self.walk(*t, scope, expanding_helper, locals)?;
                let value = self.walk(*v, scope, expanding_helper, locals)?;
                let name = Self::binder_name(scope.len());
                scope.push(name.clone());
                let body = self.binder_body(*body, scope, expanding_helper, locals)?;
                scope.pop();
                format!("(let {name} : {ty} := {value}; {body})")
            }
            CoreNode::Nat { v } => format!("({v})"),
            CoreNode::String { v } => {
                let value: String = v
                    .iter()
                    .map(|scalar| {
                        char::from_u32(*scalar).ok_or_else(|| internal("invalid string scalar"))
                    })
                    .collect::<Result<_, _>>()?;
                format!("{:?}", value)
            }
            CoreNode::Projection { n, x, .. } => {
                format!("({n} {})", self.walk(*x, scope, expanding_helper, locals)?)
            }
        })
    }

    fn body_with_shares(
        &self,
        root: usize,
        scope: &mut Vec<String>,
        expanding_helper: Option<usize>,
        inherited: &BTreeMap<usize, String>,
    ) -> Result<String, Diagnostic> {
        let mut candidates = Vec::new();
        same_scope_shared(
            self.module,
            root,
            self.shared_open,
            self.requirements,
            scope.len(),
            &mut BTreeSet::new(),
            &mut candidates,
        );
        candidates.retain(|candidate| *candidate != root && !inherited.contains_key(candidate));
        let mut locals = inherited.clone();
        let mut bindings = Vec::new();
        for candidate in candidates {
            let value = self.walk(candidate, scope, expanding_helper, &locals)?;
            let name = format!("llshare{candidate}_{}", scope.len());
            bindings.push((name.clone(), value));
            locals.insert(candidate, name);
        }
        let mut body = self.walk(root, scope, expanding_helper, &locals)?;
        for (name, value) in bindings.into_iter().rev() {
            body = format!("(let {name} := {value}; {body})");
        }
        Ok(body)
    }

    fn binder_body(
        &self,
        root: usize,
        scope: &mut Vec<String>,
        expanding_helper: Option<usize>,
        inherited: &BTreeMap<usize, String>,
    ) -> Result<String, Diagnostic> {
        // A printer-introduced let between adjacent lambdas changes how
        // Lean's expected-type elaborator aligns implicit binders.  Keep the
        // binder spine contiguous and begin local sharing at its body.
        if matches!(self.module.nodes.get(root), Some(CoreNode::Lambda { .. })) {
            self.walk(root, scope, expanding_helper, inherited)
        } else {
            self.body_with_shares(root, scope, expanding_helper, inherited)
        }
    }

    fn helper_reference(&self, root: usize) -> String {
        let levels = level_parameters_in(self.module, root);
        format!("(@LexLeanCore.node{root}{})", level_params(&levels))
    }

    fn application_head(
        &self,
        root: usize,
        scope: &mut Vec<String>,
        expanding_helper: Option<usize>,
        locals: &BTreeMap<usize, String>,
    ) -> Result<String, Diagnostic> {
        if let Some(name) = locals.get(&root) {
            return Ok(format!("@{name}"));
        }
        if self.helpers.contains(&root) && expanding_helper != Some(root) {
            let levels = level_parameters_in(self.module, root);
            return Ok(format!("@LexLeanCore.node{root}{}", level_params(&levels)));
        }
        if let Some(CoreNode::Const { n, u }) = self.module.nodes.get(root) {
            return Ok(format!("@{n}{}", Self::universes(u)));
        }
        if let Some(CoreNode::BVar { i }) = self.module.nodes.get(root) {
            let name = scope
                .get(scope.len().checked_sub(i + 1).ok_or_else(|| {
                    internal(format!("bound variable {i} escapes scope {}", scope.len()))
                })?)
                .ok_or_else(|| internal(format!("absent bound variable {i}")))?;
            return Ok(format!("@{name}"));
        }
        Ok(format!(
            "({})",
            self.walk(root, scope, expanding_helper, locals)?
        ))
    }
}

struct Sharing {
    closed: BTreeSet<usize>,
    open: BTreeSet<usize>,
    requirements: Vec<usize>,
}

fn sharing(core: &CoreModule) -> Sharing {
    let mut requirements: Vec<usize> = Vec::with_capacity(core.nodes.len());
    let mut references = vec![0usize; core.nodes.len()];
    for node in &core.nodes {
        let requirement = match node {
            CoreNode::BVar { i } => i.saturating_add(1),
            CoreNode::App { f, x } => {
                references[*f] = references[*f].saturating_add(1);
                references[*x] = references[*x].saturating_add(1);
                requirements[*f].max(requirements[*x])
            }
            CoreNode::Lambda { t, v, .. } | CoreNode::Forall { t, v, .. } => {
                references[*t] = references[*t].saturating_add(1);
                references[*v] = references[*v].saturating_add(1);
                requirements[*t].max(requirements[*v].saturating_sub(1))
            }
            CoreNode::Let { t, v, body, .. } => {
                references[*t] = references[*t].saturating_add(1);
                references[*v] = references[*v].saturating_add(1);
                references[*body] = references[*body].saturating_add(1);
                requirements[*t]
                    .max(requirements[*v])
                    .max(requirements[*body].saturating_sub(1))
            }
            CoreNode::Projection { x, .. } => {
                references[*x] = references[*x].saturating_add(1);
                requirements[*x]
            }
            CoreNode::Sort { .. }
            | CoreNode::Const { .. }
            | CoreNode::Nat { .. }
            | CoreNode::String { .. } => 0,
        };
        requirements.push(requirement);
    }
    for declaration in &core.declarations {
        references[declaration.r#type] = references[declaration.r#type].saturating_add(1);
        if let Some(value) = declaration.value {
            references[value] = references[value].saturating_add(1);
        }
    }
    let shared: Vec<usize> = core
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            let composite = matches!(
                node,
                CoreNode::App { .. }
                    | CoreNode::Lambda { .. }
                    | CoreNode::Forall { .. }
                    | CoreNode::Let { .. }
                    | CoreNode::Projection { .. }
            );
            (composite
                && requirements[index] == 0
                && references[index] > 1
                && core.proof_nodes.binary_search(&index).is_err())
            .then_some(index)
        })
        .collect();
    let closed = shared
        .iter()
        .copied()
        .filter(|index| requirements[*index] == 0)
        .collect();
    let open = core
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            let composite = matches!(
                node,
                CoreNode::App { .. }
                    | CoreNode::Lambda { .. }
                    | CoreNode::Forall { .. }
                    | CoreNode::Let { .. }
                    | CoreNode::Projection { .. }
            );
            (composite
                && requirements[index] > 0
                && references[index] > 1
                && core.proof_nodes.binary_search(&index).is_err())
            .then_some(index)
        })
        .collect();
    Sharing {
        closed,
        open,
        requirements,
    }
}

fn same_scope_shared(
    core: &CoreModule,
    root: usize,
    shared: &BTreeSet<usize>,
    requirements: &[usize],
    scope_depth: usize,
    seen: &mut BTreeSet<usize>,
    out: &mut Vec<usize>,
) {
    if !seen.insert(root) {
        return;
    }
    match &core.nodes[root] {
        CoreNode::App { f, x } => {
            same_scope_shared(core, *f, shared, requirements, scope_depth, seen, out);
            same_scope_shared(core, *x, shared, requirements, scope_depth, seen, out);
        }
        CoreNode::Projection { x, .. } => {
            same_scope_shared(core, *x, shared, requirements, scope_depth, seen, out);
        }
        // Binder domains and let values are in the present scope; binder
        // bodies establish their own local-sharing region while rendering.
        CoreNode::Lambda { t, .. } | CoreNode::Forall { t, .. } => {
            same_scope_shared(core, *t, shared, requirements, scope_depth, seen, out);
        }
        CoreNode::Let { t, v, .. } => {
            same_scope_shared(core, *t, shared, requirements, scope_depth, seen, out);
            same_scope_shared(core, *v, shared, requirements, scope_depth, seen, out);
        }
        CoreNode::BVar { .. }
        | CoreNode::Sort { .. }
        | CoreNode::Const { .. }
        | CoreNode::Nat { .. }
        | CoreNode::String { .. } => {}
    }
    if shared.contains(&root) && requirements[root] <= scope_depth {
        out.push(root);
    }
}

fn constants_in(core: &CoreModule, roots: impl IntoIterator<Item = usize>) -> BTreeSet<String> {
    let mut constants = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut work: Vec<usize> = roots.into_iter().collect();
    while let Some(root) = work.pop() {
        if !seen.insert(root) {
            continue;
        }
        match &core.nodes[root] {
            CoreNode::Const { n, .. } | CoreNode::Projection { n, .. } => {
                constants.insert(n.clone());
                if let CoreNode::Projection { x, .. } = &core.nodes[root] {
                    work.push(*x);
                }
            }
            CoreNode::App { f, x } => {
                work.push(*f);
                work.push(*x);
            }
            CoreNode::Lambda { t, v, .. } | CoreNode::Forall { t, v, .. } => {
                work.push(*t);
                work.push(*v);
            }
            CoreNode::Let { t, v, body, .. } => {
                work.push(*t);
                work.push(*v);
                work.push(*body);
            }
            CoreNode::BVar { .. }
            | CoreNode::Sort { .. }
            | CoreNode::Nat { .. }
            | CoreNode::String { .. } => {}
        }
    }
    constants
}

fn collect_level_parameters(level: &CoreLevel, parameters: &mut BTreeSet<String>) {
    match level {
        CoreLevel::Zero => {}
        CoreLevel::Succ(inner) => collect_level_parameters(inner, parameters),
        CoreLevel::Max(pair) | CoreLevel::IMax(pair) => {
            collect_level_parameters(&pair.0, parameters);
            collect_level_parameters(&pair.1, parameters);
        }
        CoreLevel::Param(name) => {
            parameters.insert(name.clone());
        }
    }
}

fn level_parameters_in(core: &CoreModule, root: usize) -> Vec<String> {
    let mut parameters = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut work = vec![root];
    while let Some(node) = work.pop() {
        if !seen.insert(node) {
            continue;
        }
        match &core.nodes[node] {
            CoreNode::Sort { l } => collect_level_parameters(l, &mut parameters),
            CoreNode::Const { u, .. } => {
                for level in u {
                    collect_level_parameters(level, &mut parameters);
                }
            }
            CoreNode::App { f, x } => {
                work.push(*f);
                work.push(*x);
            }
            CoreNode::Lambda { t, v, .. } | CoreNode::Forall { t, v, .. } => {
                work.push(*t);
                work.push(*v);
            }
            CoreNode::Let { t, v, body, .. } => {
                work.push(*t);
                work.push(*v);
                work.push(*body);
            }
            CoreNode::Projection { x, .. } => work.push(*x),
            CoreNode::BVar { .. } | CoreNode::Nat { .. } | CoreNode::String { .. } => {}
        }
    }
    parameters.into_iter().collect()
}

fn generated_owners(core: &CoreModule) -> BTreeMap<String, String> {
    let mut owners = BTreeMap::new();
    for declaration in &core.declarations {
        let Some(inductive) = &declaration.inductive else {
            continue;
        };
        for constructor in &inductive.constructors {
            owners.insert(constructor.clone(), declaration.name.clone());
        }
        owners.insert(
            format!("{}.rec", declaration.name),
            declaration.name.clone(),
        );
        if let Some(structure) = &inductive.structure {
            for field in &structure.fields {
                owners.insert(field.projection.clone(), declaration.name.clone());
            }
        }
    }
    let suffixes = [
        "recOn",
        "casesOn",
        "noConfusion",
        "noConfusionType",
        "_sizeOf_inst",
        "_sizeOf_1",
        "ctorIdx",
        "ctorElim",
        "ctorElimType",
        "below",
        "ibelow",
        "brecOn",
        "binductionOn",
    ];
    for declaration in &core.declarations {
        if !declaration.generated || owners.contains_key(&declaration.name) {
            continue;
        }
        if let Some(owner) = core.declarations.iter().find(|candidate| {
            candidate.inductive.is_some()
                && suffixes
                    .iter()
                    .any(|suffix| declaration.name == format!("{}.{}", candidate.name, suffix))
        }) {
            owners.insert(declaration.name.clone(), owner.name.clone());
            continue;
        }
        for (constructor, owner) in owners.clone() {
            if [
                "elim",
                "inj",
                "injEq",
                "sizeOf_spec",
                "noConfusion",
                "_flat_ctor",
            ]
            .iter()
            .any(|suffix| declaration.name == format!("{constructor}.{suffix}"))
            {
                owners.insert(declaration.name.clone(), owner);
                break;
            }
        }
    }
    owners
}

fn emission_order(core: &CoreModule) -> Result<Vec<&CoreDeclaration>, Diagnostic> {
    let emitted: BTreeMap<&str, &CoreDeclaration> = core
        .declarations
        .iter()
        .filter(|row| !row.generated)
        .map(|row| (row.name.as_str(), row))
        .collect();
    let owners = generated_owners(core);
    let rows: BTreeMap<&str, &CoreDeclaration> = core
        .declarations
        .iter()
        .map(|row| (row.name.as_str(), row))
        .collect();
    let mut dependencies: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    for (name, declaration) in &emitted {
        let mut roots = vec![declaration.r#type];
        if let Some(value) = declaration.value {
            roots.push(value);
        }
        if let Some(inductive) = &declaration.inductive {
            for constructor in &inductive.constructors {
                if let Some(row) = rows.get(constructor.as_str()) {
                    roots.push(row.r#type);
                }
            }
        }
        let mut deps = BTreeSet::new();
        for constant in constants_in(core, roots) {
            let dependency = if emitted.contains_key(constant.as_str()) {
                Some(constant)
            } else {
                owners.get(&constant).cloned()
            };
            if let Some(dependency) = dependency {
                if dependency != *name {
                    deps.insert(dependency);
                }
            }
        }
        dependencies.insert(name, deps);
    }
    let mut done = BTreeSet::new();
    let mut order = Vec::with_capacity(emitted.len());
    while order.len() < emitted.len() {
        let Some((&name, declaration)) = emitted.iter().find(|(name, _)| {
            !done.contains(**name)
                && dependencies.get(**name).is_some_and(|deps| {
                    deps.iter()
                        .all(|dependency| done.contains(dependency.as_str()))
                })
        }) else {
            let remaining = emitted
                .keys()
                .filter(|name| !done.contains(**name))
                .take(8)
                .copied()
                .collect::<Vec<_>>()
                .join(", ");
            return Err(internal(format!(
                "declaration dependency cycle or absent generated owner through: {remaining}"
            )));
        };
        done.insert(name);
        order.push(*declaration);
    }
    Ok(order)
}

fn level_params(levels: &[String]) -> String {
    if levels.is_empty() {
        String::new()
    } else {
        format!(".{{{}}}", levels.join(", "))
    }
}

const LEAN_CORE_DECODER: &str = r#"
namespace LexLeanCore.Runtime

private def fail {α : Type} (message : String) : Except String α := .error message

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def stringField (json : Json) (name : String) : Except String String := do
  (← field json name).getStr?

private def natField (json : Json) (name : String) : Except String Nat := do
  (← field json name).getNat?

private def boolField (json : Json) (name : String) : Except String Bool := do
  (← field json name).getBool?

private def arrayField (json : Json) (name : String) : Except String (Array Json) := do
  (← field json name).getArr?

private def optionalField (json : Json) (name : String) : Option Json :=
  match json.getObjVal? name with
  | .ok value => some value
  | .error _ => none

private def nameOf (value : String) : Name :=
  value.splitOn "." |>.foldl (fun name part => name.str part) .anonymous

private partial def levelOf (json : Json) : Except String Level := do
  match ← stringField json "k" with
  | "z" => pure .zero
  | "s" => pure (.succ (← levelOf (← field json "a")))
  | "m" | "i" =>
      let values ← (← field json "a").getArr?
      let some left := values[0]? | fail "core level pair lacks its left value"
      let some right := values[1]? | fail "core level pair lacks its right value"
      if values.size != 2 then fail "core level pair has extra values"
      let left ← levelOf left
      let right ← levelOf right
      if (← stringField json "k") == "m" then pure (.max left right) else pure (.imax left right)
  | "p" => pure (.param (nameOf (← stringField json "a")))
  | kind => fail s!"unknown core level kind '{kind}'"

private def levelsOf (json : Json) : Except String (List Level) := do
  let values ← json.getArr?
  values.toList.mapM levelOf

private def namesOf (json : Json) : Except String (List Name) := do
  let values ← json.getArr?
  values.toList.mapM fun value => do pure (nameOf (← value.getStr?))

private def binderOf (value : String) : Except String BinderInfo :=
  match value with
  | "e" => pure .default
  | "i" => pure .implicit
  | "s" => pure .strictImplicit
  | "c" => pure .instImplicit
  | kind => fail s!"unknown core binder kind '{kind}'"

private def nodeAt (nodes : Array Expr) (index : Nat) : Except String Expr :=
  match nodes[index]? with
  | some node => .ok node
  | none => fail s!"core node reference {index} is out of range"

private def nodeOf (nodes : Array Expr) (json : Json) : Except String Expr := do
  match ← stringField json "k" with
  | "b" => pure (.bvar (← natField json "i"))
  | "s" => pure (.sort (← levelOf (← field json "l")))
  | "c" => pure (.const (nameOf (← stringField json "n")) (← levelsOf (← field json "u")))
  | "a" => pure (.app (← nodeAt nodes (← natField json "f")) (← nodeAt nodes (← natField json "x")))
  | "l" => pure (.lam `_ (← nodeAt nodes (← natField json "t"))
      (← nodeAt nodes (← natField json "v")) (← binderOf (← stringField json "b")))
  | "p" => pure (.forallE `_ (← nodeAt nodes (← natField json "t"))
      (← nodeAt nodes (← natField json "v")) (← binderOf (← stringField json "b")))
  | "e" => pure (.letE `_ (← nodeAt nodes (← natField json "t"))
      (← nodeAt nodes (← natField json "v")) (← nodeAt nodes (← natField json "body"))
      (← boolField json "d"))
  | "n" =>
      let value ← stringField json "v"
      let some value := value.toNat? | fail s!"invalid core natural literal '{value}'"
      pure (.lit (.natVal value))
  | "t" =>
      let values ← (← field json "v").getArr?
      let chars ← values.toList.mapM fun value => do pure (Char.ofNat (← value.getNat?))
      pure (.lit (.strVal (String.ofList chars)))
  | "j" => pure (.proj (nameOf (← stringField json "s")) (← natField json "i")
      (← nodeAt nodes (← natField json "x")))
  | kind => fail s!"unknown core node kind '{kind}'"

private def liftString {α : Type} : Except String α → CoreM α
  | .ok value => pure value
  | .error message => throwError message

private def findDeclaration (declarations : Array Json) (name : String) : CoreM Json := do
  for declaration in declarations do
    if (← liftString (stringField declaration "name")) == name then return declaration
  throwError s!"core declaration '{name}' is absent"

private def addOneUnchecked (nodes : Array Expr) (declarations : Array Json)
    (json : Json) : CoreM Unit := do
  if ← liftString (boolField json "generated") then return
  let nameString ← liftString (stringField json "name")
  let name := nameOf nameString
  let levelParams ← liftString (namesOf (← liftString (field json "levels")))
  let type ← liftString (nodeAt nodes (← liftString (natField json "type")))
  let kindString ← liftString (stringField json "kind")
  match kindString with
  | "inductive" =>
      let metadata ← liftString (field json "inductive")
      let numParams ← liftString (natField metadata "num_params")
      let constructorNames ← liftString (arrayField metadata "constructors")
      let mut constructors : List Constructor := []
      for constructorName in constructorNames do
        let constructorName ← liftString constructorName.getStr?
        let row ← findDeclaration declarations constructorName
        let constructorType ← liftString (nodeAt nodes (← liftString (natField row "type")))
        constructors := constructors.concat { name := nameOf constructorName, type := constructorType }
      Lean.addDecl (.inductDecl levelParams numParams [{ name, type, ctors := constructors }] false)
        (forceExpose := true)
  | "abbrev" | "definition" =>
      let valueIndex ← liftString (natField json "value")
      let value ← liftString (nodeAt nodes valueIndex)
      let metadata ← liftString (field json "reducibility")
      let reducibilityKind ← liftString (stringField metadata "kind")
      let hints ← match reducibilityKind with
        | "abbrev" => pure ReducibilityHints.abbrev
        | "opaque" => pure (default : ReducibilityHints)
        | "regular" => pure (ReducibilityHints.regular
            (UInt32.ofNat (← liftString (natField metadata "height"))))
        | other => throwError s!"unknown core reducibility kind '{other}'"
      Lean.addDecl (.defnDecl { name, levelParams, type, value, hints, safety := .safe })
        (forceExpose := true)
  | "theorem" =>
      let value ← liftString (nodeAt nodes (← liftString (natField json "value")))
      Lean.addDecl (.thmDecl { name, levelParams, type, value }) (forceExpose := true)
  | "constructor" | "recursor" =>
      throwError s!"non-generated primitive core declaration '{nameString}'"
  | kind => throwError s!"unknown core declaration kind '{kind}'"

private def addOne (nodes : Array Expr) (declarations : Array Json) (json : Json) : CoreM Unit := do
  let name ← liftString (stringField json "name")
  try
    addOneUnchecked nodes declarations json
  catch error =>
    throwError m!"native core declaration '{name}':{indentD error.toMessageData}"

def decodeAndAdd (data : String) : CoreM Unit := do
  let document ← liftString (Json.parse data)
  let nodeRows ← liftString (arrayField document "nodes")
  let mut nodes : Array Expr := #[]
  for row in nodeRows do
    nodes := nodes.push (← liftString (nodeOf nodes row))
  let declarations ← liftString (arrayField document "declarations")
  let order ← liftString (arrayField document "order")
  for index in order do
    let index ← liftString index.getNat?
    let some declaration := declarations[index]? |
      throwError s!"core declaration order index {index} is out of range"
    addOne nodes declarations declaration
  for declaration in declarations do
    if (← liftString (stringField declaration "kind")) == "inductive" then
      let metadata ← liftString (field declaration "inductive")
      if let some structureData := optionalField metadata "structure" then
        let name := nameOf (← liftString (stringField declaration "name"))
        let fieldRows ← liftString (arrayField structureData "fields")
        let mut fields : Array StructureFieldInfo := #[]
        for row in fieldRows do
          let subobject? : Option Name ← match optionalField row "subobject" with
            | some value => pure (some (nameOf (← liftString value.getStr?)))
            | none => pure none
          let autoParam? : Option Expr ← match optionalField row "auto_param" with
            | some value => pure (some (← liftString (nodeAt nodes (← liftString value.getNat?))))
            | none => pure none
          let fieldName := nameOf (← liftString (stringField row "name"))
          let projFn := nameOf (← liftString (stringField row "projection"))
          let binderInfo ← liftString (binderOf (← liftString (stringField row "binder")))
          fields := fields.push {
            fieldName
            projFn
            subobject?
            binderInfo
            autoParam? }
        setEnv <| Lean.registerStructure (← getEnv) { structName := name, fields }
  for declaration in declarations do
    if (← liftString (stringField declaration "kind")) == "inductive" then
      let metadata ← liftString (field declaration "inductive")
      if let some structureData := optionalField metadata "structure" then
        let name := nameOf (← liftString (stringField declaration "name"))
        let parentRows ← liftString (arrayField structureData "parents")
        let mut parents : Array StructureParentInfo := #[]
        for row in parentRows do
          let structName := nameOf (← liftString (stringField row "name"))
          let subobject ← liftString (boolField row "subobject")
          let projFn := nameOf (← liftString (stringField row "projection"))
          parents := parents.push {
            structName
            subobject
            projFn }
        Lean.setStructureParents name parents
  for declaration in declarations do
    if (← liftString (stringField declaration "kind")) == "inductive" then
      let metadata ← liftString (field declaration "inductive")
      if (optionalField metadata "structure").isSome then
        discard <| Lean.computeStructureResolutionOrder
          (nameOf (← liftString (stringField declaration "name"))) true
  for declaration in declarations do
    let name := nameOf (← liftString (stringField declaration "name"))
    let status ← match ← liftString (stringField declaration "transparency") with
      | "reducible" => pure ReducibilityStatus.reducible
      | "semireducible" => pure ReducibilityStatus.semireducible
      | "irreducible" => pure ReducibilityStatus.irreducible
      | "implicit-reducible" => pure ReducibilityStatus.implicitReducible
      | other => throwError s!"unknown core transparency '{other}'"
    Lean.setReducibilityStatus name status
  for declaration in declarations do
    let generated ← liftString (boolField declaration "generated")
    if !generated && (← liftString (boolField declaration "class")) then
      let name := nameOf (← liftString (stringField declaration "name"))
      match Lean.addClass (← getEnv) name with
      | .ok env => setEnv env
      | .error message => throwError message
  for declaration in declarations do
    if let some metadata := optionalField declaration "instance" then
      let name := nameOf (← liftString (stringField declaration "name"))
      let priority ← liftString (natField metadata "priority")
      let attributeKind ← match ← liftString (stringField metadata "attribute") with
        | "global" => pure AttributeKind.global
        | "local" => pure AttributeKind.local
        | "scoped" => pure AttributeKind.scoped
        | other => throwError s!"unknown core instance attribute kind '{other}'"
      Lean.Meta.MetaM.run' <| Lean.Meta.addInstance name attributeKind priority
      let expectedRows ← liftString (arrayField metadata "synthesis_order")
      let mut expected : Array Nat := #[]
      for row in expectedRows do expected := expected.push (← liftString row.getNat?)
      let some actual := (Lean.Meta.instanceExtension.getState (← getEnv)
          |>.instanceNames.find? name) |
        throwError s!"core instance '{name}' was not registered"
      unless actual.synthOrder == expected do
        throwError s!"core instance '{name}' reconstructed synthesis order {actual.synthOrder.toList} instead of {expected.toList}"

end LexLeanCore.Runtime
"#;

/// Render a native core module as Lean.  The emitted command reconstructs
/// semantic `Expr` and `Declaration` values, and `Lean.addDecl` submits every
/// declaration to the kernel checker.  No backend text or unchecked
/// environment mutation is accepted by this path.
pub fn render_lean(checked: &CheckedModule, core: &CoreModule) -> Result<Emitter, Diagnostic> {
    let mut emitter = Emitter::new();
    let node = emitter.node("core-lean-kernel-module");
    let mut text = String::from("module\n");
    for import in &core.imports {
        text.push_str(&format!("public import {import}\n"));
    }
    text.push_str(
        "import Lean\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 1000000000\nset_option Elab.async false\n\nopen Lean\n",
    );
    text.push_str(LEAN_CORE_DECODER);
    let positions: BTreeMap<&str, usize> = core
        .declarations
        .iter()
        .enumerate()
        .map(|(index, row)| (row.name.as_str(), index))
        .collect();
    let order = emission_order(core)?
        .into_iter()
        .map(|declaration| {
            positions
                .get(declaration.name.as_str())
                .copied()
                .ok_or_else(|| internal(format!("absent declaration `{}`", declaration.name)))
        })
        .collect::<Result<Vec<_>, _>>()?;
    // Keep the lexicographic field order produced by serde_json's canonical
    // object map while serializing the typed DAG directly.  A second dynamic
    // JSON tree is prohibitively expensive for foundation-sized modules.
    #[derive(serde::Serialize)]
    struct CorePayload<'a> {
        declarations: &'a [CoreDeclaration],
        imports: &'a [String],
        nodes: &'a [CoreNode],
        order: &'a [usize],
        proof_nodes: &'a [usize],
        spec: &'a str,
    }
    let payload = CorePayload {
        declarations: &core.declarations,
        imports: &core.imports,
        nodes: &core.nodes,
        order: &order,
        proof_nodes: &core.proof_nodes,
        spec: &core.spec,
    };
    let payload = serde_json::to_string(&payload)
        .map_err(|error| internal(format!("cannot encode core module: {error}")))?;
    let mut chunks = Vec::new();
    let mut chunk = String::new();
    for character in payload.chars() {
        if chunk.len() >= 500_000 {
            chunks.push(std::mem::take(&mut chunk));
        }
        chunk.push(character);
    }
    if !chunk.is_empty() {
        chunks.push(chunk);
    }
    text.push_str("\nrun_cmd Lean.Elab.Command.liftCoreM (LexLeanCore.Runtime.decodeAndAdd (\n");
    for (index, chunk) in chunks.iter().enumerate() {
        text.push_str("  ");
        text.push_str(&format!("{chunk:?}"));
        if index + 1 != chunks.len() {
            text.push_str(" ++");
        }
        text.push('\n');
    }
    text.push_str("))\n");
    emit_chunk(
        &mut emitter,
        checked,
        node,
        &text,
        "core-lean-kernel-module",
    );
    Ok(emitter)
}

fn tex_escape(text: &str) -> String {
    let mut out = String::new();
    for character in text.chars() {
        match character {
            '\\' => out.push_str("\\textbackslash{}"),
            '{' => out.push_str("\\{"),
            '}' => out.push_str("\\}"),
            '#' => out.push_str("\\#"),
            '$' => out.push_str("\\$"),
            '%' => out.push_str("\\%"),
            '&' => out.push_str("\\&"),
            '_' => out.push_str("\\_"),
            '^' => out.push_str("\\^{}"),
            '~' => out.push_str("\\~{}"),
            other if other.is_ascii() => out.push(other),
            other => out.push_str(&format!("<U+{:04X}>", u32::from(other))),
        }
    }
    out
}

/// Render synchronized declaration statements and proof terms from the same
/// core DAG as canonical LaTeX.
pub fn render_latex(checked: &CheckedModule, core: &CoreModule) -> Result<Emitter, Diagnostic> {
    let mut emitter = Emitter::new();
    let preamble = emitter.node("core-latex-preamble");
    emit_chunk(
        &mut emitter,
        checked,
        preamble,
        "\\documentclass[11pt]{article}\n\\usepackage[T1]{fontenc}\n\\usepackage{amsmath,amssymb}\n\\usepackage[hidelinks]{hyperref}\n\\begin{document}\n\\begin{center}{\\LARGE Native core module}\\end{center}\n\\section*{Kernel-linked declarations}\n",
        "core-latex-preamble",
    );
    let sharing = sharing(core);
    let printer = Printer {
        module: core,
        helpers: &sharing.closed,
        shared_open: &sharing.open,
        requirements: &sharing.requirements,
    };
    for declaration in &core.declarations {
        let mut scope = Vec::new();
        let ty = printer.term(declaration.r#type, &mut scope)?;
        let mut text = format!(
            "\\subsection*{{\\texttt{{{}}}}}\n\\noindent\\texttt{{{}}}\\par\n\\noindent Axiom policy: \\texttt{{{} [{}]}}.\\par\n",
            tex_escape(&declaration.name),
            tex_escape(&ty),
            declaration.policy.kind(),
            tex_escape(&declaration.policy.axioms().join(", ")),
        );
        if let Some(value) = declaration.value {
            let mut scope = Vec::new();
            let value = printer.term(value, &mut scope)?;
            let label = if matches!(declaration.kind, CoreDeclKind::Theorem) {
                "Proof term"
            } else {
                "Defined as"
            };
            text.push_str(&format!(
                "\\noindent {label} \\texttt{{{}}}.\\par\n",
                tex_escape(&value)
            ));
        }
        let node = emitter.node("core-declaration");
        emit_chunk(&mut emitter, checked, node, &text, "core-latex-declaration");
    }
    let end = emitter.node("core-latex-preamble");
    emit_chunk(
        &mut emitter,
        checked,
        end,
        "\\end{document}\n",
        "core-latex-preamble",
    );
    Ok(emitter)
}
