use super::{
    Output,
    expression::{Generator, Ordering},
};
use crate::{
    ast::{TypedClauseGuard, TypedExpr},
    docvec,
    exhaustiveness::{
        Body, BoundValue, CompiledCase, Decision, FallbackCheck, RuntimeCheck, Variable,
    },
    format::break_block,
    javascript::expression::{string, string_from_eco},
    pretty::{Document, Documentable, join, line, nil},
    strings::convert_string_escape_chars,
};
use ecow::{EcoString, eco_format};
use std::{collections::HashMap, sync::OnceLock};

pub static ASSIGNMENT_VAR: &str = "$";

pub fn print<'a, 'generator, 'module>(
    compiled_case: &'a CompiledCase,
    clauses: Vec<(&'a TypedExpr, Option<&'a TypedClauseGuard>)>,
    subjects: &'a [TypedExpr],
    expression_generator: &'generator mut Generator<'module, 'a>,
) -> Output<'a> {
    // The case subjects might be repeated in the generated code, so we want to
    // assign those to variables (if they're not already ones) and use those;
    // otherwise we'd end up calling the same functions multiple times, which
    // would change the program's meaning!
    let (subjects_values, assignments): (Vec<_>, Vec<_>) =
        assign_subjects(expression_generator, subjects)
            .into_iter()
            .unzip();

    let mut printer = DecisionPrinter {
        clauses,
        expression_generator,
        variable_values: HashMap::new(),
    };

    for (variable, subject) in compiled_case.subject_variables.iter().zip(subjects_values) {
        printer.set_variable_value(variable, subject);
    }

    let decision = printer.decision(&compiled_case.tree)?;

    // Then if there's any assignment we write those before the generated
    // decision tree.
    let mut subject_assignments_docs = vec![];
    for (var, subject) in assignments.into_iter().zip(subjects) {
        let Some(var) = var else { continue };
        let value = expression_generator
            .not_in_tail_position(Some(Ordering::Strict), |this| this.wrap_expression(subject))?;
        subject_assignments_docs.push(let_(var, value).append(line()))
    }

    Ok(docvec![subject_assignments_docs, decision].force_break())
}

pub struct DecisionPrinter<'module, 'generator, 'a> {
    clauses: Vec<(&'a TypedExpr, Option<&'a TypedClauseGuard>)>,
    expression_generator: &'generator mut Generator<'module, 'a>,
    variable_values: HashMap<usize, EcoString>,
}

impl<'module, 'generator, 'a> DecisionPrinter<'module, 'generator, 'a> {
    fn set_variable_value(&mut self, variable: &Variable, value: EcoString) {
        let _ = self.variable_values.insert(variable.id, value);
    }

    fn variable_value(&self, variable: &Variable) -> EcoString {
        self.variable_values
            .get(&variable.id)
            .expect("pattern variable used before assignment")
            .clone()
    }

    fn decision(&mut self, decision: &'a Decision) -> Output<'a> {
        match decision {
            Decision::Fail => unreachable!("Invalid decision tree reached code generation"),
            Decision::Run { body } => self.decision_body(body),
            Decision::Switch {
                var,
                choices,
                fallback,
                fallback_check,
            } => self.switch(var, choices, fallback, fallback_check),
            Decision::Guard {
                guard,
                if_true,
                if_false,
            } => self.decision_guard(*guard, if_true, if_false),
        }
    }

    fn decision_body(&mut self, body: &'a Body) -> Output<'a> {
        let Body {
            bindings,
            clause_index,
        } = body;

        let bindings = join(
            bindings
                .iter()
                .map(|binding| self.decision_binding(binding)),
            line(),
        );

        let consequence = self.expression_generator.expression_flattening_blocks(
            &self
                .clauses
                .get(*clause_index)
                .expect("decision tree invalid clause index")
                .0,
        )?;

        Ok(if bindings.is_empty() {
            consequence
        } else {
            docvec![bindings, line(), consequence]
        })
    }

    fn decision_binding(&mut self, binding: &'a (EcoString, BoundValue)) -> Document<'a> {
        let (original_variable_name, assigned_value) = binding;
        let variable_name = self
            .expression_generator
            .next_local_var(original_variable_name);
        let assigned_value = match assigned_value {
            BoundValue::Variable(variable) => self.variable_value(variable).to_doc(),
            BoundValue::LiteralString(value) => string(value),
        };

        let_(variable_name.clone(), assigned_value)
    }

    fn switch(
        &mut self,
        var: &'a Variable,
        choices: &'a [(RuntimeCheck, Box<Decision>)],
        fallback: &'a Decision,
        fallback_check: &'a FallbackCheck,
    ) -> Output<'a> {
        match choices {
            // If there's just a single choice we can just generate the code for
            // it: no need to do any checking, we know it must match!
            [] => {
                if let FallbackCheck::RuntimeCheck { check } = fallback_check {
                    self.record_check_assignments(var, check);
                }
                self.decision(fallback)
            }
            _ => {
                let mut first = true;
                let mut if_ = nil();
                for (check, decision) in choices {
                    self.record_check_assignments(var, check);
                    let body = self.inside_new_scope(|this| this.decision(decision))?;
                    let check_doc = self.runtime_check(var, check);
                    let branch = if first {
                        first = false;
                        docvec!["if (", check_doc, ") "]
                    } else {
                        docvec![" else if (", check_doc, ") "]
                    };

                    if_ = if_.append(docvec![branch, break_block(body)]);
                }

                // In case there's some new variables we can extract after the
                // successful check we store those. But we don't need to perform
                // the check itself: the type system makes sure that, if we ever
                // get here, the check is going to match no matter what!
                if let FallbackCheck::RuntimeCheck { check } = fallback_check {
                    self.record_check_assignments(var, check);
                }

                let body = self.inside_new_scope(|this| this.decision(fallback))?;
                if body.is_empty() {
                    Ok(if_)
                } else {
                    let else_ = docvec![" else ", break_block(body)];
                    Ok(docvec![if_, else_])
                }
            }
        }
    }

    fn inside_new_scope<A, F>(&mut self, run: F) -> A
    where
        F: Fn(&mut Self) -> A,
    {
        let old_scope = self.expression_generator.current_scope_vars.clone();
        let output = run(self);
        self.expression_generator.current_scope_vars = old_scope;
        output
    }

    fn decision_guard(
        &mut self,
        guard: usize,
        if_true: &'a Body,
        if_false: &'a Decision,
    ) -> Output<'a> {
        let guard = self
            .clauses
            .get(guard)
            .expect("invalid clause index")
            .1
            .expect("missing guard should");
        let (check, if_true) = self.inside_new_scope(|this| {
            // All the knowledge about what values are assigned is inside the
            // final `if_true` body. So we have to generate it before the check
            // to make sure we know of all the variables it might be referencing.
            let if_true = this.decision_body(if_true)?;
            let check: Document<'_> = todo!("generate code for the guard check");
            Ok((check, if_true))
        })?;

        let if_ = docvec!["if (", check, ") ", break_block(if_true)];
        let if_false = self.inside_new_scope(|this| this.decision(if_false))?;
        if if_false.is_empty() {
            Ok(if_)
        } else {
            let else_ = docvec![" else ", break_block(if_false)];
            Ok(docvec![if_, else_])
        }
    }

    fn runtime_check(&mut self, var: &Variable, runtime_check: &RuntimeCheck) -> Document<'a> {
        let var_value = self.variable_value(var);
        match runtime_check {
            RuntimeCheck::String { value } => {
                docvec![var_value, " === ", string_from_eco(value.clone())]
            }
            RuntimeCheck::Int { value } | RuntimeCheck::Float { value } => {
                docvec![var_value, " === ", value]
            }

            RuntimeCheck::StringPrefix { prefix, .. } => docvec![
                var_value,
                ".startsWith(",
                string_from_eco(prefix.clone()),
                ")"
            ],

            RuntimeCheck::BitArray { value } => docvec!["TODO"],

            // When checking on a tuple there's always going to be a single choice
            // and the code generation will always skip generating the check for it
            // as the type system ensures it must match.
            RuntimeCheck::Tuple { .. } => unreachable!("tried generating runtime check for tuple"),

            RuntimeCheck::Variant { match_, .. } if var.type_.is_bool() => {
                if match_.name() == "True" {
                    var_value.to_doc()
                } else {
                    docvec!["!", var_value]
                }
            }

            RuntimeCheck::Variant { match_, .. } if var.type_.is_result() => {
                docvec![var_value, ".is", match_.name(), "()"]
            }

            RuntimeCheck::Variant { match_, .. } => {
                let qualification = match_
                    .module()
                    .map(|module| eco_format!("${module}."))
                    .unwrap_or_default();

                docvec![var_value, " instanceof ", qualification, match_.name()]
            }
            RuntimeCheck::NonEmptyList { .. } => docvec!["!", var_value, ".hasLength(0)"],
            RuntimeCheck::EmptyList => docvec![var_value, ".hasLength(0)"],
        }
    }

    fn record_check_assignments(&mut self, var: &Variable, check: &RuntimeCheck) {
        let value = self.variable_value(var);
        match check {
            RuntimeCheck::Int { .. }
            | RuntimeCheck::Float { .. }
            | RuntimeCheck::String { .. }
            | RuntimeCheck::BitArray { .. }
            | RuntimeCheck::EmptyList => (),

            RuntimeCheck::StringPrefix { rest, prefix } => {
                let prefix_size = utf16_no_escape_len(prefix);
                self.set_variable_value(rest, eco_format!("{value}.slice({prefix_size})"));
            }

            RuntimeCheck::Tuple { elements, .. } => {
                for (i, element) in elements.iter().enumerate() {
                    self.set_variable_value(element, eco_format!("{value}[{i}]"));
                }
            }

            RuntimeCheck::Variant { fields, labels, .. } => {
                for (i, field) in fields.iter().enumerate() {
                    let access = match labels.get(&i) {
                        Some(label) => eco_format!("{value}.{label}"),
                        None => eco_format!("{value}[{i}]"),
                    };
                    self.set_variable_value(field, access);
                }
            }

            RuntimeCheck::NonEmptyList { first, rest } => {
                self.set_variable_value(first, eco_format!("{value}.head"));
                self.set_variable_value(rest, eco_format!("{value}.tail"));
            }
        }
    }
}

fn let_<'a>(variable_name: EcoString, value: Document<'a>) -> Document<'a> {
    docvec!["let ", variable_name, " = ", value, ";"]
}

/// Calculates the length of str as utf16 without escape characters.
///
fn utf16_no_escape_len(str: &EcoString) -> usize {
    convert_string_escape_chars(str).encode_utf16().count()
}

fn assign_subjects<'a>(
    expression_generator: &mut Generator<'_, 'a>,
    subjects: &'a [TypedExpr],
) -> Vec<(EcoString, Option<EcoString>)> {
    let mut out = Vec::with_capacity(subjects.len());
    for subject in subjects {
        out.push(assign_subject(expression_generator, subject))
    }
    out
}

fn assign_subject<'a>(
    expression_generator: &mut Generator<'_, 'a>,
    subject: &'a TypedExpr,
) -> (EcoString, Option<EcoString>) {
    static ASSIGNMENT_VAR_ECO_STR: OnceLock<EcoString> = OnceLock::new();

    match subject {
        // If the value is a variable we don't need to assign it to a new
        // variable, we can the value expression safely without worrying about
        // performing computation or side effects multiple times.
        TypedExpr::Var {
            name, constructor, ..
        } if constructor.is_local_variable() => (expression_generator.local_var(name), None),
        // If it's not a variable we need to assign it to a variable
        // to avoid rendering the subject expression multiple times
        _ => {
            let subject = expression_generator
                .next_local_var(ASSIGNMENT_VAR_ECO_STR.get_or_init(|| ASSIGNMENT_VAR.into()));
            (subject.clone(), Some(subject))
        }
    }
}
