//! Deterministic Lean and LaTeX lowering for language-1.1 semantic modules.

use crate::artifact::source_map::MapRole;
use crate::backend::{EmitSource, Emitter};
use crate::code;
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::{
    MemberRef, SemanticAssignment, SemanticBranch, SemanticDeclaration, SemanticModule,
    SemanticParameter, SemanticProof, SemanticProofBranch, SemanticReflection,
    SemanticReflectionComparison, SemanticReflectionField, SemanticTerm, SemanticType,
};
use crate::link::CheckedModule;
use crate::source::coverage::Origin;

struct Render<'a> {
    prefix: &'a str,
}

fn term_uses(term: &SemanticTerm, local: &str) -> bool {
    let pair = |left: &SemanticTerm, right: &SemanticTerm| {
        term_uses(left, local) || term_uses(right, local)
    };
    match term {
        SemanticTerm::Var { name } => name == local,
        SemanticTerm::Nat { .. }
        | SemanticTerm::Bool { .. }
        | SemanticTerm::Unit
        | SemanticTerm::Nil { .. }
        | SemanticTerm::InstanceValue { .. } => false,
        SemanticTerm::Cons { head, tail }
        | SemanticTerm::Eq {
            left: head,
            right: tail,
        }
        | SemanticTerm::Le {
            left: head,
            right: tail,
        }
        | SemanticTerm::Lt {
            left: head,
            right: tail,
        }
        | SemanticTerm::Add {
            left: head,
            right: tail,
        }
        | SemanticTerm::Beq {
            left: head,
            right: tail,
        }
        | SemanticTerm::Ble {
            left: head,
            right: tail,
        }
        | SemanticTerm::Blt {
            left: head,
            right: tail,
        }
        | SemanticTerm::And {
            left: head,
            right: tail,
        }
        | SemanticTerm::PropAnd {
            left: head,
            right: tail,
        }
        | SemanticTerm::Or {
            left: head,
            right: tail,
        }
        | SemanticTerm::Implies {
            premise: head,
            conclusion: tail,
        }
        | SemanticTerm::Iff {
            left: head,
            right: tail,
        } => pair(head, tail),
        SemanticTerm::Not { value } | SemanticTerm::Project { value, .. } => {
            term_uses(value, local)
        }
        SemanticTerm::Record { fields, .. } => fields
            .iter()
            .any(|assignment| term_uses(&assignment.value, local)),
        SemanticTerm::Constructor { arguments, .. } | SemanticTerm::Call { arguments, .. } => {
            arguments.iter().any(|argument| term_uses(argument, local))
        }
        SemanticTerm::If {
            condition,
            then_value,
            else_value,
        } => {
            term_uses(condition, local)
                || term_uses(then_value, local)
                || term_uses(else_value, local)
        }
        SemanticTerm::Match {
            scrutinee,
            branches,
        } => {
            term_uses(scrutinee, local)
                || branches.iter().any(|branch| term_uses(&branch.body, local))
        }
        SemanticTerm::Forall { binder, body } => binder.name != local && term_uses(body, local),
    }
}

fn reflected_projection(record: &str, field: &SemanticReflectionField) -> String {
    format!("({record}).{}", field.field)
}

fn reflected_bool(record: &str, fields: &[SemanticReflectionField]) -> String {
    let field = &fields[0];
    let comparison = format!(
        "Nat.beq ({}) ({})",
        reflected_projection(record, field),
        field.expected
    );
    if fields.len() == 1 {
        comparison
    } else {
        format!("({comparison} && {})", reflected_bool(record, &fields[1..]))
    }
}

fn reflected_prop(record: &str, fields: &[SemanticReflectionField]) -> String {
    let field = &fields[0];
    let comparison = format!(
        "({} = {})",
        reflected_projection(record, field),
        field.expected
    );
    if fields.len() == 1 {
        comparison
    } else {
        format!(
            "({comparison} /\\ {})",
            reflected_prop(record, &fields[1..])
        )
    }
}

fn reflected_iff(fields: &[SemanticReflectionField]) -> String {
    if fields.len() == 1 {
        "llBeqBridge _ _".to_owned()
    } else {
        format!(
            "Iff.trans (llAndBridge _ _) (and_congr (llBeqBridge _ _) ({}))",
            reflected_iff(&fields[1..])
        )
    }
}

impl Render<'_> {
    fn member(&self, member: &MemberRef) -> String {
        member.module.as_ref().map_or_else(
            || member.name.clone(),
            |module| format!("{}.{}.{}", self.prefix, module, member.name),
        )
    }

    fn ty(&self, ty: &SemanticType) -> String {
        match ty {
            SemanticType::Type => "Type".to_owned(),
            SemanticType::Parameter { name } => name.clone(),
            SemanticType::Nat => "Nat".to_owned(),
            SemanticType::Bool => "Bool".to_owned(),
            SemanticType::Prop => "Prop".to_owned(),
            SemanticType::Unit => "Unit".to_owned(),
            SemanticType::List { element } => format!("List ({})", self.ty(element)),
            SemanticType::Named { member, arguments } => {
                let mut out = self.member(member);
                for argument in arguments {
                    out.push_str(" (");
                    out.push_str(&self.ty(argument));
                    out.push(')');
                }
                out
            }
        }
    }

    fn parameters(&self, parameters: &[SemanticParameter]) -> String {
        parameters
            .iter()
            .map(|parameter| format!(" ({} : {})", parameter.name, self.ty(&parameter.r#type)))
            .collect()
    }

    fn recursive_equations(
        &self,
        name: &str,
        parameters: &[SemanticParameter],
        result: &SemanticType,
        recursive_argument: &str,
        body: &SemanticTerm,
    ) -> Option<String> {
        let SemanticTerm::Match {
            scrutinee,
            branches,
        } = body
        else {
            return None;
        };
        if !matches!(scrutinee.as_ref(), SemanticTerm::Var { name } if name == recursive_argument) {
            return None;
        }
        let mut text = format!("@[expose] public def {name} :");
        for parameter in parameters {
            text.push_str(&format!(
                " ({} : {}) ->",
                parameter.name,
                self.ty(&parameter.r#type)
            ));
        }
        text.push_str(&format!(" {}\n", self.ty(result)));
        for branch in branches {
            let patterns = parameters
                .iter()
                .map(|parameter| {
                    if parameter.name == recursive_argument {
                        let binders = if branch.binders.is_empty() {
                            String::new()
                        } else {
                            format!(
                                " {}",
                                branch
                                    .binders
                                    .iter()
                                    .map(|binder| {
                                        if term_uses(&branch.body, binder) {
                                            binder.as_str()
                                        } else {
                                            "_"
                                        }
                                    })
                                    .collect::<Vec<_>>()
                                    .join(" ")
                            )
                        };
                        format!("{}{}", self.member(&branch.constructor), binders)
                    } else if term_uses(&branch.body, &parameter.name) {
                        parameter.name.clone()
                    } else {
                        format!("_{}", parameter.name)
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");
            text.push_str(&format!("  | {patterns} => {}\n", self.term(&branch.body)));
        }
        Some(text)
    }

    fn type_parameters(&self, parameters: &[String]) -> String {
        parameters
            .iter()
            .map(|parameter| format!(" ({parameter} : Type)"))
            .collect()
    }

    fn assignments(&self, assignments: &[SemanticAssignment]) -> String {
        assignments
            .iter()
            .map(|row| format!("{} := {}", row.field, self.term(&row.value)))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn branch(&self, branch: &SemanticBranch) -> String {
        let binders = if branch.binders.is_empty() {
            String::new()
        } else {
            format!(
                " {}",
                branch
                    .binders
                    .iter()
                    .map(|binder| {
                        if term_uses(&branch.body, binder) {
                            binder.as_str()
                        } else {
                            "_"
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        };
        format!(
            "| {}{} => {}",
            self.member(&branch.constructor),
            binders,
            self.term(&branch.body)
        )
    }

    #[allow(clippy::too_many_lines)]
    fn term(&self, term: &SemanticTerm) -> String {
        let binary = |operator: &str, left: &SemanticTerm, right: &SemanticTerm| {
            format!("({} {operator} {})", self.term(left), self.term(right))
        };
        match term {
            SemanticTerm::Var { name } => name.clone(),
            SemanticTerm::Nat { value } => value.clone(),
            SemanticTerm::Bool { value } => value.to_string(),
            SemanticTerm::Unit => "()".to_owned(),
            SemanticTerm::Nil { element } => format!("([] : List ({}))", self.ty(element)),
            SemanticTerm::Cons { head, tail } => {
                format!("({} :: {})", self.term(head), self.term(tail))
            }
            SemanticTerm::Record {
                r#type,
                type_arguments,
                fields,
            } => {
                let annotation = SemanticType::Named {
                    member: r#type.clone(),
                    arguments: type_arguments.clone(),
                };
                format!(
                    "({{ {} }} : {})",
                    self.assignments(fields),
                    self.ty(&annotation)
                )
            }
            SemanticTerm::Constructor {
                constructor,
                type_arguments: _,
                arguments,
            } => {
                let mut out = self.member(constructor);
                for argument in arguments {
                    out.push_str(" (");
                    out.push_str(&self.term(argument));
                    out.push(')');
                }
                out
            }
            SemanticTerm::InstanceValue { resolved, .. } => self.member(resolved),
            SemanticTerm::Project { value, field } => {
                format!("({}).{field}", self.term(value))
            }
            SemanticTerm::Call {
                function,
                arguments,
            } => {
                let mut out = self.member(function);
                for argument in arguments {
                    out.push_str(" (");
                    out.push_str(&self.term(argument));
                    out.push(')');
                }
                out
            }
            SemanticTerm::If {
                condition,
                then_value,
                else_value,
            } => format!(
                "(if {} then {} else {})",
                self.term(condition),
                self.term(then_value),
                self.term(else_value)
            ),
            SemanticTerm::Match {
                scrutinee,
                branches,
            } => format!(
                "(match {} with {})",
                self.term(scrutinee),
                branches
                    .iter()
                    .map(|branch| self.branch(branch))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            SemanticTerm::Eq { left, right } => binary("=", left, right),
            SemanticTerm::Le { left, right } => binary("<=", left, right),
            SemanticTerm::Lt { left, right } => binary("<", left, right),
            SemanticTerm::Add { left, right } => binary("+", left, right),
            SemanticTerm::Beq { left, right } => {
                format!("(Nat.beq ({}) ({}))", self.term(left), self.term(right))
            }
            SemanticTerm::Ble { left, right } => {
                format!("(Nat.ble ({}) ({}))", self.term(left), self.term(right))
            }
            SemanticTerm::Blt { left, right } => {
                format!("(Nat.blt ({}) ({}))", self.term(left), self.term(right))
            }
            SemanticTerm::And { left, right } => binary("&&", left, right),
            SemanticTerm::PropAnd { left, right } => binary("/\\", left, right),
            SemanticTerm::Or { left, right } => binary("||", left, right),
            SemanticTerm::Not { value } => format!("(!{})", self.term(value)),
            SemanticTerm::Implies {
                premise,
                conclusion,
            } => binary("->", premise, conclusion),
            SemanticTerm::Iff { left, right } => binary("<->", left, right),
            SemanticTerm::Forall { binder, body } => format!(
                "(forall ({} : {}), {})",
                binder.name,
                self.ty(&binder.r#type),
                self.term(body)
            ),
        }
    }

    fn proof_branch(&self, branch: &SemanticProofBranch, indent: usize) -> String {
        let binders = if branch.binders.is_empty() {
            String::new()
        } else {
            format!(" {}", branch.binders.join(" "))
        };
        format!(
            "{}| {}{} =>\n{}",
            "  ".repeat(indent),
            branch.constructor,
            binders,
            self.proof(&branch.proof, indent + 1)
        )
    }

    fn proof(&self, proof: &SemanticProof, indent: usize) -> String {
        let pad = "  ".repeat(indent);
        match proof {
            SemanticProof::Reflexivity => format!("{pad}rfl\n"),
            SemanticProof::Decide => format!("{pad}decide\n"),
            SemanticProof::Simplify { definitions } => format!(
                "{pad}simp only [{}]\n",
                definitions
                    .iter()
                    .map(|member| self.member(member))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            SemanticProof::Constructor { branches } => {
                let mut out = format!("{pad}constructor\n");
                for branch in branches {
                    out.push_str(&format!("{pad}·\n"));
                    out.push_str(&self.proof(branch, indent + 1));
                }
                out
            }
            SemanticProof::Cases {
                scrutinee,
                branches,
            } => {
                let mut out = format!("{pad}cases {scrutinee} with\n");
                for branch in branches {
                    out.push_str(&self.proof_branch(branch, indent));
                }
                out
            }
            SemanticProof::Induction {
                scrutinee,
                generalizing,
                branches,
            } => {
                let generalizing = if generalizing.is_empty() {
                    String::new()
                } else {
                    format!(" generalizing {}", generalizing.join(" "))
                };
                let mut out = format!("{pad}induction {scrutinee}{generalizing} with\n");
                for branch in branches {
                    out.push_str(&self.proof_branch(branch, indent));
                }
                out
            }
            SemanticProof::Congruence => format!("{pad}congr 1\n"),
            SemanticProof::BooleanReflection { reflection } => match reflection {
                SemanticReflection::List {
                    parameter,
                    values,
                    boolean_definition,
                    proposition_definition,
                    comparison,
                } => {
                    let boolean = self.member(boolean_definition);
                    let proposition = self.member(proposition_definition);
                    let mut out = format!(
                        "{pad}have llAndBridge : ∀ left right : Bool, ((left && right) = true) ↔ left = true ∧ right = true := by\n{pad}  intro left right\n{pad}  cases left <;> cases right <;> decide\n"
                    );
                    if matches!(comparison, SemanticReflectionComparison::NatBeq) {
                        out.push_str(&format!(
                            "{pad}have llBeqRefl : ∀ value : Nat, Nat.beq value value = true := by\n{pad}  intro value\n{pad}  induction value with\n{pad}  | zero => rfl\n{pad}  | succ value ih => exact ih\n"
                        ));
                    }
                    out.push_str(&format!(
                        "{pad}induction {values} generalizing {parameter} with\n{pad}| nil => constructor <;> intro _ <;> rfl\n{pad}| cons llValue llRest llIH =>\n{pad}  constructor\n{pad}  · intro h\n{pad}    have hpair := (llAndBridge _ _).mp h\n"
                    ));
                    match comparison {
                        SemanticReflectionComparison::NatBeq => out.push_str(&format!(
                            "{pad}    exact And.intro (Nat.eq_of_beq_eq_true hpair.left) ((llIH ({parameter} + 1)).mp hpair.right)\n{pad}  · intro h\n{pad}    have hleft : Nat.beq {parameter} llValue = true := h.left ▸ llBeqRefl {parameter}\n{pad}    have hright : {boolean} ({parameter} + 1) llRest = true := (llIH ({parameter} + 1)).mpr h.right\n{pad}    exact (llAndBridge _ _).mpr (And.intro hleft hright)\n"
                        )),
                        SemanticReflectionComparison::NatBlt => out.push_str(&format!(
                            "{pad}    exact And.intro (Nat.le_of_ble_eq_true hpair.left) ((llIH {parameter}).mp hpair.right)\n{pad}  · intro h\n{pad}    have hleft : Nat.blt llValue {parameter} = true := Nat.ble_eq_true_of_le h.left\n{pad}    have hright : {boolean} {parameter} llRest = true := (llIH {parameter}).mpr h.right\n{pad}    exact (llAndBridge _ _).mpr (And.intro hleft hright)\n"
                        )),
                    }
                    let _ = proposition;
                    out
                }
                SemanticReflection::Record {
                    record,
                    boolean_definition,
                    proposition_definition,
                    fields,
                } => {
                    let _ = (
                        self.member(boolean_definition),
                        self.member(proposition_definition),
                    );
                    format!(
                        "{pad}have llAndBridge : ∀ left right : Bool, ((left && right) = true) ↔ left = true ∧ right = true := by\n{pad}  intro left right\n{pad}  cases left <;> cases right <;> decide\n{pad}have llBeqRefl : ∀ value : Nat, Nat.beq value value = true := by\n{pad}  intro value\n{pad}  induction value with\n{pad}  | zero => rfl\n{pad}  | succ value ih => exact ih\n{pad}have llBeqBridge : ∀ left right : Nat, Nat.beq left right = true ↔ left = right := by\n{pad}  intro left right\n{pad}  constructor\n{pad}  · exact Nat.eq_of_beq_eq_true\n{pad}  · intro h\n{pad}    cases h\n{pad}    exact llBeqRefl left\n{pad}change (({}) = true) ↔ {}\n{pad}exact {}\n",
                        reflected_bool(record, fields),
                        reflected_prop(record, fields),
                        reflected_iff(fields)
                    )
                }
            },
            SemanticProof::Apply { theorem, arguments } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| format!(" ({})", self.term(argument)))
                    .collect::<String>();
                format!("{pad}exact {}{arguments}\n", self.member(theorem))
            }
        }
    }
}

fn emit(checked: &CheckedModule, text: &str, kind: &str) -> Emitter {
    let mut emitter = Emitter::new();
    let node = emitter.node(kind);
    emitter.piece(
        text,
        kind,
        Origin::Metadata {
            owner: "lexlean.core::semanticdata".to_owned(),
        },
        EmitSource::File(0, checked.normalized.len()),
        MapRole::Declaration,
        node,
    );
    emitter
}

/// Render one semantic module as prose-free Lean.
pub fn render_lean(
    checked: &CheckedModule,
    module: &SemanticModule,
    module_prefix: &str,
) -> Result<Emitter, Diagnostic> {
    let render = Render {
        prefix: module_prefix,
    };
    let document = &checked.document;
    let mut text = String::from("module\npublic import Init\n");
    for import in &document.imports {
        text.push_str(&format!("public import {module_prefix}.{import}\n"));
    }
    text.push_str("set_option autoImplicit false\nnamespace ");
    text.push_str(&document.lean_module);
    text.push('\n');
    for declaration in &module.declarations {
        text.push('\n');
        match declaration {
            SemanticDeclaration::Structure {
                name,
                type_parameters,
                parameters,
                fields,
            } => {
                text.push_str(&format!(
                    "public structure {name}{}{} where\n",
                    render.type_parameters(type_parameters),
                    render.parameters(parameters)
                ));
                for field in fields {
                    text.push_str(&format!(
                        "  {} : {}\n",
                        field.name,
                        render.ty(&field.r#type)
                    ));
                }
            }
            SemanticDeclaration::Class {
                name,
                type_parameters,
                parameters,
                fields,
            } => {
                text.push_str(&format!(
                    "public class {name}{}{} where\n",
                    render.type_parameters(type_parameters),
                    render.parameters(parameters)
                ));
                for field in fields {
                    text.push_str(&format!(
                        "  {} : {}\n",
                        field.name,
                        render.ty(&field.r#type)
                    ));
                }
            }
            SemanticDeclaration::Instance {
                name,
                class,
                arguments,
                priority,
                fields,
            } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| format!(" ({})", render.ty(argument)))
                    .collect::<String>();
                text.push_str(&format!(
                    "public instance (priority := {priority}) {name} : {}{arguments} where\n",
                    render.member(class)
                ));
                for field in fields {
                    text.push_str(&format!(
                        "  {} := {}\n",
                        field.field,
                        render.term(&field.value)
                    ));
                }
            }
            SemanticDeclaration::Inductive {
                name,
                type_parameters,
                parameters,
                constructors,
            } => {
                text.push_str(&format!(
                    "public inductive {name}{}{} where\n",
                    render.type_parameters(type_parameters),
                    render.parameters(parameters)
                ));
                for constructor in constructors {
                    let fields = constructor
                        .fields
                        .iter()
                        .map(|field| format!(" (_ : {})", render.ty(field)))
                        .collect::<String>();
                    text.push_str(&format!("  | {}{fields}\n", constructor.name));
                }
            }
            SemanticDeclaration::Definition {
                name,
                parameters,
                result,
                body,
                recursive_argument,
            } => {
                if let Some(recursive_argument) = recursive_argument {
                    let equations = render
                        .recursive_equations(name, parameters, result, recursive_argument, body)
                        .ok_or_else(|| {
                            Diagnostic::new(
                                code!("LLI9001"),
                                "phase lean-backend: recursive definition is not a top-level structural match",
                            )
                        })?;
                    text.push_str(&equations);
                } else {
                    text.push_str(&format!(
                        "@[expose] public def {name}{} : {} := {}\n",
                        render.parameters(parameters),
                        render.ty(result),
                        render.term(body)
                    ));
                }
            }
            SemanticDeclaration::Theorem {
                name,
                parameters,
                statement,
                proof,
                ..
            } => {
                text.push_str(&format!(
                    "public theorem {name}{} : {} := by\n{}",
                    render.parameters(parameters),
                    render.term(statement),
                    render.proof(proof, 1)
                ));
            }
        }
    }
    text.push_str("\nend ");
    text.push_str(&document.lean_module);
    text.push('\n');
    if text.contains("--") {
        return Err(Diagnostic::new(
            code!("LLI9001"),
            "phase lean-backend: semantic lowering produced a comment token",
        ));
    }
    Ok(emit(checked, &text, "semantic-lean-module"))
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

/// Render the same semantic module as canonical explanatory LaTeX.
pub fn render_latex(
    checked: &CheckedModule,
    module: &SemanticModule,
    module_prefix: &str,
) -> Result<Emitter, Diagnostic> {
    let render = Render {
        prefix: module_prefix,
    };
    let mut text = String::from(
        "\\documentclass[11pt]{article}\n\\usepackage[T1]{fontenc}\n\\usepackage{amsmath,amssymb}\n\\begin{document}\n\\section*{Semantic declarations}\n",
    );
    for declaration in &module.declarations {
        text.push_str(&format!(
            "\\subsection*{{\\texttt{{{}}}}}\n\\noindent Kind: \\texttt{{{}}}.\\par\n",
            tex_escape(declaration.name()),
            declaration.kind()
        ));
        match declaration {
            SemanticDeclaration::Definition { result, body, .. } => text.push_str(&format!(
                "\\noindent Type: \\texttt{{{}}}.\\par\n\\noindent Definition: \\texttt{{{}}}.\\par\n",
                tex_escape(&render.ty(result)),
                tex_escape(&render.term(body))
            )),
            SemanticDeclaration::Theorem {
                statement, axioms, ..
            } => {
                let policy = if axioms.is_empty() {
                    "none".to_owned()
                } else {
                    format!("exact [{}]", axioms.join(", "))
                };
                text.push_str(&format!(
                    "\\noindent Statement: \\texttt{{{}}}.\\par\n\\noindent Axiom policy: \\texttt{{{}}}.\\par\n",
                    tex_escape(&render.term(statement)),
                    tex_escape(&policy)
                ));
            }
            _ => {}
        }
    }
    text.push_str("\\end{document}\n");
    Ok(emit(checked, &text, "semantic-latex-module"))
}
