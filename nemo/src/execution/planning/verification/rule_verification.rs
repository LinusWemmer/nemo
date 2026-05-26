//! Gernerates the RuleVerifier of a program
use std::collections::{HashMap, HashSet};

use crate::execution::planning::verification::rule_verification::z3_translation::RuleTranslator;

use crate::{
    execution::planning::normalization::{program::NormalizedProgram, rule::NormalizedRule},
    rule_model::components::{tag::Tag, term::primitive::variable::Variable},
};

use z3::ast::exists_const;
use z3::{
    self, FuncDecl, Sort,
    ast::{Ast, Bool, Int},
};
use z3::{Goal, Solver, Tactic};

pub mod z3_restriction;
pub mod z3_translation;

/// Struct for converting and verifying rules with z3
/// TODO: split this up into two components, the translator and the verifier tool
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

    /// Verifies a whether a rule satisfies it's annotations
    /// TODO: probably change to special IH terms
    /// body /\ assertions on body |= assertions on head
    pub fn verify_rule(program: &NormalizedProgram, rule: &NormalizedRule) {
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
        let verifier = RuleTranslator::new_with_predicates(predicate_to_z3_fun);

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
        let body_instance = verifier.translate_rule(rule, &var_cache, program);
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
                    "Violation for {} found with var assigment {}",
                    head_assertions[0], var_interpretation
                )
            }
        }
    }

    /// gets filter atoms for head?
    /// TODO: change this to some sort of horn rule/maximize/minimize as before
    /// => we only want to keep
    pub fn propagate_filters(rule: &NormalizedRule, _program: &NormalizedProgram) -> Vec<Bool> {
        let verifier = RuleTranslator::new();

        let tactic_qe = Tactic::new("qe");
        let goal = Goal::new(false, false, false);

        let var_cache: HashMap<Variable, Int> = rule
            .variables()
            .map(|v| {
                (
                    v.clone(),
                    Int::fresh_const(v.name().expect("Anon vars not supported yet")),
                )
            })
            .collect();

        let body_operations: Vec<Bool> = rule
            .operations()
            .iter()
            .map(|b| {
                verifier
                    .translate_operation(b, &var_cache)
                    .as_bool()
                    .expect("Top level operations should have Sort Bool")
            })
            .collect();

        let body_translation = Bool::and(&body_operations);
        //TODO: insert restrictions&specs here !IMPORTANT!

        let head_variables: HashSet<&Variable> = rule
            .head()
            .iter()
            .flat_map(|atom| atom.variables())
            .collect();

        let body_vars: HashSet<&Variable> = rule
            .variables()
            .filter(|v| !head_variables.contains(*v))
            .collect();

        let args: Vec<&dyn Ast> = body_vars
            .iter()
            .map(|v| var_cache.get(v).expect("variable should be registered"))
            .map(|v| -> &dyn Ast { v })
            .collect();

        goal.assert(&exists_const(&args, &[], &body_translation));

        let result = tactic_qe
            .apply(&goal, None)
            .expect("qe tactic failed")
            .list_subgoals()
            .collect::<Vec<Goal>>();

        // Return the filters if qe succeded, otherwise none
        // might have issues with termination. Think about IR for now?
        if let Some(goal) = result.first() {
            let filters = goal.get_formulas();
            println!("{:#?}", filters);
            filters
        } else {
            Vec::new()
        }
    }
}
