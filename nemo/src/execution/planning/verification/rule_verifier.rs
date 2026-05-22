//! Gernerates the RuleVerifier of a program

use std::collections::HashMap;

use crate::execution::planning::normalization::global_annotation::NormalizedGlobalAnnotation;
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

use z3::Solver;
use z3::{
    self, FuncDecl, Sort,
    ast::{Ast, Bool, Dynamic, Int},
};

/// Struct for converting rules
#[derive(Debug, Copy, Clone)]
pub struct RuleVerifier {
    fresh_var_counter: usize,
}

impl RuleVerifier {
    /// Creates a new [RuleVerifier]
    pub fn new() -> Self {
        Self {
            fresh_var_counter: 0,
        }
    }
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
        var_cache: &HashMap<Variable, Int>,
        program: &NormalizedProgram,
    ) -> Vec<Bool> {
        let mut body_terms = Vec::new();
        for atom in rule.positive() {
            let smt_atom = self.translate_body_atom(atom, &var_cache, predicate_to_z3_fun);
            body_terms.push(smt_atom);

            body_terms.extend(
                program
                    .predicate_to_global_annotation(&atom.predicate())
                    .iter()
                    .map(|a| self.translate_body_assertion(a, atom, var_cache)),
            );
        }

        //TODO: gather possible propagated restrictions (each instance should be an conjunction, and disjunt all of them)
        // test if this is computationally feasable
        let body_operations = rule.operations().iter().map(|b| {
            self.translate_operation(b, &var_cache)
                .as_bool()
                .expect("Top level operations should have Sort Bool")
        });

        body_terms.extend(body_operations);

        // TODO: maybe move the ground to the body somehow, support rules with only one head maybe?
        // Build the rules
        /*rule.head()
        .iter()
        .map(|h| self.translate_head_atom(h, &var_cache, predicate_to_z3_fun))
        .map(|h| h.implies(&body))
        .collect();*/
        body_terms
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
                    //TODO: map the vars to new variables, or even better the appropriate head var
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

    /// Translates the assertion for the head predicate into smt representation
    /// TODO: test with groundstuff in head
    pub fn translate_head_assertion(
        &self,
        assertion: &NormalizedGlobalAnnotation,
        head_predicate: &HeadAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Bool {
        let substitution = head_predicate.terms().zip(assertion.variables());

        // Map the head atom terms to variables in the assertion body
        // This should probably work, but could be a source of bugs
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

    /// Verifies a whether a rule satisfies it's annotations
    /// TODO: probably change to special IH terms
    /// body /\ assertions on body |= assertions on head
    pub fn verify_rule(program: &NormalizedProgram, rule: &NormalizedRule) {
        let verifier = RuleVerifier::new();
        let solver = Solver::new();

        let bool_sort = Sort::bool();
        let int_sort = Sort::int();
        // Register all predicates of the rule
        let mut predicate_to_z3_fun: HashMap<Tag, FuncDecl> = HashMap::new();

        for (tag, arity) in rule.predicates() {
            let args_sort = vec![&int_sort; arity];
            let pred = FuncDecl::new(tag.name(), &args_sort, &bool_sort);
            predicate_to_z3_fun.insert(tag, pred);
        }
        let var_cache: HashMap<Variable, Int> = rule
            .variables()
            .map(|v| {
                (
                    v.clone(),
                    Int::fresh_const(v.name().expect("Anon vars not supported yet")),
                )
            })
            .collect();

        // Translate rule body
        let body_instance =
            verifier.translate_rule(rule, &predicate_to_z3_fun, &var_cache, program);
        for term in body_instance {
            solver.assert(term);
        }

        // Translate assertion for head (For now only one head predicate & only one assertion)
        let head = &rule.head()[0];
        let head_assertions = program.predicate_to_global_annotation(&head.predicate());
        let head_restriction =
            verifier.translate_head_assertion(head_assertions[0], head, &var_cache);
        solver.assert(&head_restriction.not());

        let smt = solver.to_smt2();
        println!("{smt}");
        match solver.check() {
            z3::SatResult::Unsat => println!("Validated: spec holds"),
            z3::SatResult::Unknown => println!("Could not validate (unknown)"),
            z3::SatResult::Sat => {
                let model = solver.get_model().expect("Sat model should exist");
                let var_interpretation: String = head
                    .variables()
                    .map(|v| {
                        let inter = model
                            .get_const_interp(var_cache.get(v).expect("Var should be in cache"))
                            .expect("Counterexample should exist for violation");
                        format!("{} : {}", v, inter)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                println!("{rule}");
                println!(
                    "Violation for {} found with model {}",
                    head_assertions[0], var_interpretation
                )
            }
        }
    }
}
