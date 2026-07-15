//! Translates normalized rules into a z3 representation, defined by struct [RuleTranslator]

use std::collections::HashMap;

use nemo_physical::datavalues::DataValue;
use z3::{
    FuncDecl,
    ast::{Ast, Bool, Dynamic, Int},
};

use crate::{
    execution::planning::normalization::{
        atom::{body::BodyAtom, ground::GroundAtom, head::HeadAtom},
        global_annotation::NormalizedGlobalAnnotation,
        operation::Operation,
        program::NormalizedProgram,
        rule::NormalizedRule,
    },
    rule_model::components::{
        tag::Tag,
        term::primitive::{Primitive, variable::Variable},
    },
};

/// Struct for translating rules to a z3 representation for verification
#[derive(Debug)]
pub struct RuleTranslator {
    /// Maps Predicate Tags to z3 function declarations
    predicate_to_z3_fun: HashMap<Tag, FuncDecl>,
}

impl RuleTranslator {
    /// Creates a new [RuleTranslator]
    pub fn new() -> Self {
        let predicate_to_z3_fun = HashMap::default();
        Self {
            predicate_to_z3_fun,
        }
    }

    /// Creates a new rules translator with a map from predicate Tags to z3 functions
    pub fn new_with_predicates(predicate_to_z3_fun: HashMap<Tag, FuncDecl>) -> Self {
        Self {
            predicate_to_z3_fun,
        }
    }
}

impl RuleTranslator {
    /// Translates a (normalized) body atom according to tau
    pub fn translate_body_atom(&self, atom: &BodyAtom, var_cache: &HashMap<Variable, Int>) -> Bool {
        let predicate = self
            .predicate_to_z3_fun
            .get(&atom.predicate())
            .expect("predicate should be registered");

        let mut var_list = Vec::new();
        for var in atom.terms() {
            var_list.push(
                var_cache
                    .get(var)
                    .expect("Variable should be registered")
                    .clone(),
            );
        }

        let args: Vec<&dyn Ast> = var_list.iter().map(|v| -> &dyn Ast { v }).collect();

        predicate
            .apply(&args)
            .as_bool()
            .expect("translating body atom went wrong")
    }

    /// Translates a (normalized) head atom according to tau
    pub fn translate_head_atom(&self, atom: &HeadAtom, var_cache: &HashMap<Variable, Int>) -> Bool {
        let predicate = self
            .predicate_to_z3_fun
            .get(&atom.predicate())
            .expect("predicate should be registered");

        let mut term_list = Vec::new();
        for term in atom.terms() {
            term_list.push(self.translate_primitive(term, var_cache));
        }

        let args: Vec<&dyn Ast> = term_list.iter().map(|v| -> &dyn Ast { v }).collect();

        predicate
            .apply(&args)
            .as_bool()
            .expect("translating head atom went wrong")
    }

    /// Translate a ground atom TODO: allow other types than int (also in general needed)
    /// => Actuall not needed
    /*pub fn translate_ground_atom(&self, atom: &GroundAtom) -> Bool {
        let bool_sort = Sort::bool();
        let int_sort = Sort::int();

        let args_sort = vec![&int_sort; atom.arity()];
        let pred = FuncDecl::new(atom.predicate().name(), &args_sort, &bool_sort);

        let term_list: Vec<Int> = atom
            .terms()
            .map(|t| Int::from_i64(t.value().to_i64_unchecked()))
            .collect();

        // I have no idead why this works, it also seems very convoluted
        let args: Vec<&dyn Ast> = term_list.iter().map(|v| -> &dyn Ast { v }).collect();

        pred.apply(&args)
            .as_bool()
            .expect("translating groudnd atom went wrong")
    }*/

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

    /// Translates an operation into z3 ast according to tau
    /// TODO: this need to be checked actually
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
            Operation::Opreation { kind, subterms } => {
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

    /// Translates the global assertion body
    /// TODO: add predicate
    /// Maybe the varcache has to use a hashset as basis?
    pub fn translate_body_assertion(
        &self,
        assertion: &NormalizedGlobalAnnotation,
        rule_predicate: &BodyAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Bool {
        // define the variable substitution: TODO: turn these into
        let substitution = rule_predicate.terms().zip(assertion.variables());

        // This sort of defines a "substitution"
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
    ) -> Vec<Bool> {
        let mut body_terms = Vec::new();

        //TODO: should this be moved to the verification, i.e. rule and assertion seperately?
        for atom in rule.positive() {
            //let smt_atom = self.translate_body_atom(atom, &var_cache);
            //body_terms.push(smt_atom); TODO: maybe still neccesary?

            body_terms.extend(
                program
                    .predicate_to_global_annotation(&atom.predicate())
                    .iter()
                    .map(|a| self.translate_body_assertion(a, atom, var_cache)),
            );
        }

        // test if this is computationally feasible
        let body_operations = rule.operations().iter().map(|b| {
            self.translate_operation(b, &var_cache)
                .as_bool()
                .expect("Top level operations should have Sort Bool")
        });

        body_terms.extend(body_operations);

        body_terms
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
