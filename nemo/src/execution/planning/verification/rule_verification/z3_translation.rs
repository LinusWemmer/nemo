//! Translates normalized rules into a z3 representation, defined by struct [RuleTranslator]

use std::collections::HashMap;

use nemo_physical::datavalues::DataValue;
use z3::ast::{Ast, Bool, Dynamic, Int};

use crate::{
    execution::planning::normalization::{
        atom::{body::BodyAtom, ground::GroundAtom, head::HeadAtom},
        global_annotation::NormalizedGlobalAnnotation,
        operation::Operation,
        program::NormalizedProgram,
        rule::NormalizedRule,
        termination_annotation::NormalizedTerminationAnnotation,
    },
    rule_model::components::{
        tag::Tag,
        term::primitive::{Primitive, variable::Variable},
    },
};

/// Struct for translating rules to a z3 representation for verification
#[derive(Debug, Clone, Copy)]
pub struct RuleTranslator {}

impl RuleTranslator {
    /// Creates a new [RuleTranslator]
    pub fn new() -> Self {
        Self {}
    }
}

impl RuleTranslator {
    /// Translates a primitive into an int for now
    pub fn translate_primitive(&self, prim: &Primitive, var_cache: &HashMap<Variable, Int>) -> Int {
        match prim {
            Primitive::Variable(variable) => var_cache
                .get(variable)
                .expect("variable should be registered")
                .clone(),
            Primitive::Ground(ground_term) => Int::from_i64(ground_term.value().to_i64_unchecked()),
        }
    }

    /// Translates an operation into z3 ast
    /// #panics if the formula isn't well formed
    pub fn translate_operation(
        &self,
        op: &Operation,
        var_cache: &HashMap<Variable, Int>,
    ) -> Dynamic {
        match op {
            Operation::Primitive(primitive) => {
                self.translate_primitive(primitive, var_cache).into()
            }
            Operation::Operation { kind, subterms } => {
                let left = self.translate_operation(
                    subterms.first().expect("Formula wasn't well formed"),
                    var_cache,
                );
                let right = self.translate_operation(
                    subterms.get(1).expect("Formula wasn't well formed"),
                    var_cache,
                );
                match kind {
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::Equal => {
                        left.as_int().expect("msg").eq(right.as_int().expect("msg")).into()
                    }
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::Unequals => {
                        left.as_int().expect("msg").ne(right.as_int().expect("msg")).into()
                    },
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::NumericSum => {
                        (left.as_int().expect("msg") + right.as_int().expect("msg")).into()
                    },
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::NumericSubtraction => {
                        (left.as_int().expect("msg") - right.as_int().expect("msg")).into()
                    },
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::NumericProduct => {
                        (left.as_int().expect("msg") * right.as_int().expect("msg")).into()
                    },
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::NumericDivision => {
                        (left.as_int().expect("msg") / right.as_int().expect("msg")).into()
                    },
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::NumericGreaterthaneq => {
                        left.as_int().expect("msg").ge(right.as_int().expect("msg")).into()
                    },
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::NumericGreaterthan => {
                        left.as_int().expect("msg").gt(right.as_int().expect("msg")).into()
                    },
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::NumericLessthaneq => {
                        left.as_int().expect("msg").le(right.as_int().expect("msg")).into()
                    },
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::NumericLessthan => {
                        left.as_int().expect("msg").lt(right.as_int().expect("msg")).into()
                    },
                    _ => panic!("unsupported operation used")
                }
            }
        }
    }

    /// Translates the termination annotation statement for the given body atom
    pub fn translate_termination_annotation_body(
        &self,
        annotation: &NormalizedTerminationAnnotation,
        body_predicate: &BodyAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Int {
        let annotation_head: &BodyAtom = annotation.head();
        let substitution = annotation_head.terms().zip(body_predicate.terms());

        let var_sub: HashMap<Variable, Int> = substitution
            .map(|(v_annotation, v_predicate)| {
                (
                    v_annotation.clone(),
                    var_cache
                        .get(v_predicate)
                        .expect("Variable should be in cache")
                        .clone(),
                )
            })
            .collect();
        self.translate_operation(annotation.body(), &var_sub)
            .as_int()
            .expect("termination annotation body should be an integer expression")
    }

    /// Translates the termination annotation statement for the given head atom
    pub fn translate_termination_annotation_head(
        &self,
        annotation: &NormalizedTerminationAnnotation,
        head_predicate: &HeadAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Int {
        let annotation_head: &BodyAtom = annotation.head();
        let substitution = annotation_head.terms().zip(head_predicate.terms());

        let prim_cache: HashMap<Variable, Int> = substitution
            .map(|(v, p)| match p {
                Primitive::Variable(head_var) => (
                    v.clone(),
                    var_cache
                        .get(head_var)
                        .expect("Variable should be in cache")
                        .clone(),
                ),
                Primitive::Ground(ground_term) => (
                    v.clone(),
                    Int::from_i64(ground_term.value().to_i64_unchecked()),
                ),
            })
            .collect();
        self.translate_operation(annotation.body(), &prim_cache)
            .as_int()
            .expect("termination annotation body should be an integer expression")
    }

    /// Maybe the varcache has to use a hashset as basis?
    pub fn translate_body_assertion(
        &self,
        assertion: &NormalizedGlobalAnnotation,
        rule_predicate: &BodyAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Bool {
        // define the variable substitution:
        let substitution = rule_predicate.terms().zip(assertion.variables());

        // This is only possible if all variables in the assertion head are different
        let var_sub: HashMap<Variable, Int> = substitution
            .map(|(v_rule, v_assert)| {
                (
                    v_assert.clone(),
                    var_cache
                        .get(v_rule)
                        .expect("Variable should be in cache")
                        .clone(),
                )
            })
            .collect();

        let body_constraints: Vec<Bool> = assertion
            .body()
            .iter()
            .map(|b| {
                self.translate_operation(b, &var_sub)
                    .as_bool()
                    .expect("Top level operations should have Sort Bool")
            })
            .collect();
        // Conjunction of constraints (as a single assertions assert all its things conjunctively)
        Bool::and(&body_constraints)
    }

    /// Translate a (normalized) rule
    pub fn translate_rule(
        &self,
        rule: &NormalizedRule,
        var_cache: &HashMap<Variable, Int>,
        program: &NormalizedProgram,
    ) -> (Vec<Bool>, Vec<Bool>) {
        let mut body_annotations = Vec::new();
        for atom in rule.positive() {
            body_annotations.extend(
                program
                    .predicate_to_global_annotation(&atom.predicate())
                    .iter()
                    .map(|a| self.translate_body_assertion(a, atom, var_cache)),
            );
        }

        let body_operations = rule
            .operations()
            .iter()
            .map(|b| {
                self.translate_operation(b, &var_cache)
                    .as_bool()
                    .expect("Top level operations should have Sort Bool")
            })
            .collect();

        (body_operations, body_annotations)
    }

    /// Translate a (normalized) rule, only the annotations for edb annotations are translated
    pub fn translate_rule_edb_annotations(
        &self,
        rule: &NormalizedRule,
        var_cache: &HashMap<Variable, Int>,
        program: &NormalizedProgram,
        edb_predicates: &Vec<Tag>,
    ) -> (Vec<Bool>, Vec<Bool>) {
        let mut body_annotations = Vec::new();
        for atom in rule.positive() {
            if edb_predicates.contains(&atom.predicate()) {
                body_annotations.extend(
                    program
                        .predicate_to_global_annotation(&atom.predicate())
                        .iter()
                        .map(|a| self.translate_body_assertion(a, atom, var_cache)),
                );
            }
        }

        let body_operations = rule
            .operations()
            .iter()
            .map(|b| {
                self.translate_operation(b, &var_cache)
                    .as_bool()
                    .expect("Top level operations should have Sort Bool")
            })
            .collect();

        (body_operations, body_annotations)
    }

    /// Checks whether the given operation is a filter operation
    pub fn is_filter_operation(restriction: &Bool) -> bool {
        let children = restriction.children();
        let left = children.first();
        let right = children.get(1);
        if restriction.is_app()
            && let Some(t1) = left
            && let Some(t2) = right
        {
            return (t1.is_const() || t1.is_app()) && (t2.is_const() || t2.is_app());
        }
        false
    }

    /// Translates a rule but leaves out annotations
    pub fn translate_rule_operations_without_annotations(
        &self,
        rule: &NormalizedRule,
        var_cache: &HashMap<Variable, Int>,
    ) -> Vec<Bool> {
        rule.operations()
            .iter()
            .map(|b| {
                self.translate_operation(b, &var_cache)
                    .as_bool()
                    .expect("Top level operations should have Sort Bool")
            })
            .collect()
    }

    /// Translates assertion for a fact (ground atom)
    pub fn translate_ground_assertion(
        &self,
        assertion: &NormalizedGlobalAnnotation,
        fact: &GroundAtom,
    ) -> Bool {
        let substitution = fact.terms().zip(assertion.variables());
        let prim_cache: HashMap<Variable, Int> = substitution
            .map(|(t, v)| (v.clone(), Int::from_i64(t.value().to_i64_unchecked())))
            .collect();

        let ground_term_assertion: Vec<Bool> = assertion
            .body()
            .iter()
            .map(|b| {
                self.translate_operation(b, &prim_cache)
                    .as_bool()
                    .expect("Top level operations should have Sort Bool")
            })
            .collect();
        Bool::and(&ground_term_assertion)
    }

    /// Translates the assertion for the head predicate into smt representation
    pub fn translate_head_assertion(
        &self,
        assertion: &NormalizedGlobalAnnotation,
        head_predicate: &HeadAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Bool {
        let substitution = head_predicate.terms().zip(assertion.variables());

        // Map the head atom terms to variables in the assertion body
        let prim_cache: HashMap<Variable, Int> = substitution
            .map(|(p, v)| match p {
                Primitive::Variable(head_var) => (
                    v.clone(),
                    var_cache
                        .get(head_var)
                        .expect("Variable should be in cache")
                        .clone(),
                ),
                Primitive::Ground(ground_term) => (
                    v.clone(),
                    Int::from_i64(ground_term.value().to_i64_unchecked()),
                ),
            })
            .collect();

        let head_assertions: Vec<Bool> = assertion
            .body()
            .iter()
            .map(|b| {
                self.translate_operation(b, &prim_cache)
                    .as_bool()
                    .expect("Top level operations should have Sort Bool")
            })
            .collect();

        Bool::and(&head_assertions)
    }
}
