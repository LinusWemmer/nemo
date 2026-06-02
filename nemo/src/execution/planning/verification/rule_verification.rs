//! Gernerates the RuleVerifier of a program
use std::collections::{HashMap, HashSet};

use crate::execution::planning::normalization::atom::ground::GroundAtom;
use crate::execution::planning::verification::rule_verification::{
    z3_restriction::Restriction, z3_translation::RuleTranslator,
};

use crate::{
    execution::planning::normalization::{program::NormalizedProgram, rule::NormalizedRule},
    rule_model::components::{tag::Tag, term::primitive::variable::Variable},
};

use z3::{
    self, FuncDecl, Sort,
    ast::{Ast, Bool, Int, exists_const},
};
use z3::{Goal, Solver, Tactic};

pub mod z3_restriction;
pub mod z3_translation;

/// Struct for converting and verifying rules with z3

#[derive(Debug, Clone)]
pub struct RuleVerifier {
    fresh_var_counter: usize,
    predicate_restrictions: HashMap<Tag, Restriction>,
}

impl RuleVerifier {
    /// Creates a new [RuleVerifier]
    pub fn new() -> Self {
        Self {
            fresh_var_counter: 0,
            predicate_restrictions: HashMap::new(),
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
    pub fn verify_rule(&self, program: &NormalizedProgram, rule: &NormalizedRule) {
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
        let translator = RuleTranslator::new_with_predicates(predicate_to_z3_fun);

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
        let body_instance = translator.translate_rule(rule, &var_cache, program);
        for term in body_instance {
            solver.assert(term);
        }
        // Translate propagated restrictions on body atoms
        let prop_restrictions = rule.positive().iter().filter_map(|b| {
            self.predicate_restrictions
                .get(&b.predicate())
                .and_then(|r| Some(r.get_restrictions_for_body(b, &var_cache)))
        });
        for term in prop_restrictions {
            solver.assert(&term);
        }

        // Translate assertion for head, verify each
        for head in rule.head() {
            solver.push();
            let head_atom_assertions = program.predicate_to_global_annotation(&head.predicate());
            if let Some(assertion) = head_atom_assertions.first() {
                let head_assertion =
                    translator.translate_head_assertion(assertion, head, &var_cache);
                solver.assert(&head_assertion.not());
                //let smt = solver.to_smt2();
                //println!("{smt}");
                match solver.check() {
                    z3::SatResult::Unsat => println!("Validated: spec for {assertion} holds"),
                    z3::SatResult::Unknown => println!("Could not validate (unknown)"),
                    z3::SatResult::Sat => {
                        let model = solver.get_model().expect("Sat model should exist");
                        let var_interpretation: String = head
                            .variables()
                            .map(|v| {
                                let inter = model
                                    .get_const_interp(
                                        var_cache.get(v).expect("Var should be in cache"),
                                    )
                                    .expect("Counterexample should exist for violation");
                                format!("{} : {}", v, inter)
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        println!("{rule}");
                        println!(
                            "Violation for {} found with var assigment {}",
                            assertion, var_interpretation
                        )
                    }
                }
            }
            solver.pop(1);
        }
    }

    /// Verifies whether a fact in a program satisfies it assertions
    pub fn verify_facts(&self, fact: &GroundAtom, program: &NormalizedProgram) {
        let translator = RuleTranslator::new();
        let solver = Solver::new();
        for annotation in program.predicate_to_global_annotation(&fact.predicate()) {
            solver.push();
            solver.assert(translator.translate_ground_assertion(annotation, fact));
            match solver.check() {
                z3::SatResult::Unsat => println!("{fact} does not satisfy assertion {annotation} "),
                z3::SatResult::Unknown => println!("Could not validate {fact}"),
                z3::SatResult::Sat => println!("Fact verified."),
            }
            solver.pop(1);
        }
    }

    /// Propagates filters atoms from rule body to head, returns true if new info was gained
    /// TODO: change this to some sort of horn rule/maximize/minimize as before?
    pub fn propagate_filters(
        &mut self,
        rule: &NormalizedRule,
        _program: &NormalizedProgram,
    ) -> bool {
        let translator = RuleTranslator::new();

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

        let body_operations = rule.operations().iter().map(|b| {
            translator
                .translate_operation(b, &var_cache)
                .as_bool()
                .expect("Top level operations should have Sort Bool")
        });

        // Translate propagated restrictions on body atoms
        // Introducing existential not necessary, as it is alread quantified
        let restrictions = rule.positive().iter().filter_map(|b| {
            self.predicate_restrictions
                .get(&b.predicate())
                .and_then(|r| Some(r.get_restrictions_for_body(b, &var_cache)))
        });
        let body_restrictions: Vec<Bool> = body_operations.chain(restrictions).collect();
        let body_translation = Bool::and(&body_restrictions);

        //TODO: check what is necessary, i.e. should head vars be existential based on the concrete head or something else
        // TODO: head vars for each head seperately, filter the propagate formulas for that
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
            /*for filter in &filters {
                println!("filter: {filter}");
            }*/

            let mut delta = true;

            // Temp until iteration over head implemented
            // Instead of entry check first outside of closure
            let head = &rule.head()[0];

            self.predicate_restrictions
                .entry(head.predicate())
                .and_modify(|res| {
                    delta = res.add_restriction_from_propagation(
                        &rule.head()[0],
                        &var_cache,
                        &Bool::and(&filters),
                    );
                })
                .or_insert(Restriction::new_from_propagation(
                    head,
                    &var_cache,
                    &Bool::and(&filters),
                ));
            delta
        } else {
            false
        }
    }
}
