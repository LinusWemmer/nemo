//! Gernerates the completion of a program

use std::collections::HashMap;

use crate::nemo_physical::datavalues::DataValue;
use crate::{
    execution::planning::normalization::{
        atom::{body::BodyAtom, head::HeadAtom},
        operation::Operation,
        program::NormalizedProgram,
        rule::NormalizedRule,
    },
    rule_model::components::{
        tag::Tag,
        term::primitive::{Primitive, variable::Variable},
    },
};

use z3::Fixedpoint;
use z3::{
    self, FuncDecl, Sort,
    ast::{Ast, Bool, Dynamic, Int},
};

/// Struct for converting Nemo program to FO Theories
#[derive(Debug, Copy, Clone)]
pub struct Completion {
    fresh_var_counter: usize,
}

impl Completion {
    /// Generates a new var for the program
    pub fn get_fresh_var(&mut self) -> String {
        self.fresh_var_counter += 1;
        format!("V{}", self.fresh_var_counter)
    }

    /// Translates a (normalized) body atom according to tau
    pub fn translate_body_atom(
        &self,
        atom: &BodyAtom,
        var_cache: &HashMap<Variable, Int>,
        predicate_to_z3_fun: &HashMap<Tag, FuncDecl>,
    ) -> Bool {
        let predicate = predicate_to_z3_fun
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
    pub fn translate_head_atom(
        &self,
        atom: &HeadAtom,
        var_cache: &HashMap<Variable, Int>,
        predicate_to_z3_fun: &HashMap<Tag, FuncDecl>,
    ) -> Bool {
        let predicate = predicate_to_z3_fun
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
                        left.as_bool().expect("msg").eq(right.as_bool().expect("msg")).into()
                    }
                    crate::rule_model::components::term::operation::operation_kind::OperationKind::Unequals => {
                        left.as_bool().expect("msg").ne(right.as_bool().expect("msg")).into()
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

    /// Translate a (normalized) rule (TODO: handle predicates with cache)
    pub fn translate_rule(
        &self,
        rule: &NormalizedRule,
        predicate_to_z3_fun: &HashMap<Tag, FuncDecl>,
    ) -> Vec<Bool> {
        let var_cache: HashMap<Variable, Int> = rule
            .variables()
            .map(|v| {
                (
                    v.clone(),
                    Int::fresh_const(v.name().expect("Anon vars not supported yet")),
                )
            })
            .collect();

        let body_atoms = rule
            .positive()
            .iter()
            .map(|b| self.translate_body_atom(b, &var_cache, predicate_to_z3_fun));

        let body_constraints = rule.operations().iter().map(|b| {
            self.translate_operation(b, &var_cache)
                .as_bool()
                .expect("Top level operations should have Sort Bool")
        });

        let body_terms: Vec<Bool> = body_atoms.chain(body_constraints).collect();
        let body = Bool::and(&body_terms);

        // TODO: maybe move the ground to the body somehow, support rules with only one head maybe?
        // Build the rules
        rule.head()
            .iter()
            .map(|h| self.translate_head_atom(h, &var_cache, predicate_to_z3_fun))
            .map(|h| h.implies(&body))
            .collect()
    }

    /// Translate a Datalog Program in to a set of Horn clauses
    pub fn translate_program(&self, program: &NormalizedProgram) {
        let fp = Fixedpoint::new();

        let bool_sort = Sort::bool();
        let int_sort = Sort::int();

        // Register all predicates of the program
        let mut predicate_to_z3_fun: HashMap<Tag, FuncDecl> = HashMap::new();

        for (tag, arity) in program.predicates() {
            let args_sort = vec![&int_sort; arity];
            let pred = FuncDecl::new(tag.name(), &args_sort, &bool_sort);
            fp.register_relation(&pred);
            predicate_to_z3_fun.insert(tag, pred);
        }
        for rule in program.rules() {
            let program_rules = self.translate_rule(rule, &predicate_to_z3_fun);
            for z3_rule in program_rules {
                fp.add_rule(&z3_rule, Some(&format!("{}", rule.id())));
            }
        }
    }
}
