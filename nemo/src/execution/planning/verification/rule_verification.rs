//! Gernerates the RuleVerifier of a program
use std::collections::HashMap;

use crate::execution::planning::{
    normalization::{
        atom::ground::GroundAtom, operation::Operation, program::NormalizedProgram,
        rule::NormalizedRule,
    },
    verification::rule_verification::{
        filters::Filter, z3_restriction::Restriction, z3_translation::RuleTranslator,
    },
};

use crate::rule_model::components::{tag::Tag, term::primitive::variable::Variable};

use z3::Solver;
use z3::{
    self,
    ast::{Bool, Int},
};

pub mod filters;
pub mod z3_restriction;
pub mod z3_translation;

/// Struct for converting and verifying rules with z3

#[derive(Debug, Clone)]
pub struct RuleVerifier {
    fresh_var_counter: usize,
    predicate_restrictions: HashMap<Tag, Restriction>,
    filter_predicates: Vec<Filter>,
}

impl RuleVerifier {
    /// Creates a new [RuleVerifier]
    pub fn new() -> Self {
        Self {
            fresh_var_counter: 0,
            predicate_restrictions: HashMap::new(),
            filter_predicates: Vec::new(),
        }
    }

    /// Generates a new var for the program
    pub fn get_fresh_var(&mut self) -> String {
        self.fresh_var_counter += 1;
        format!("V{}", self.fresh_var_counter)
    }

    /// Returns the predicate restrictions
    pub fn predicate_restriction(&self) -> &HashMap<Tag, Restriction> {
        &self.predicate_restrictions
    }

    /// Creates a map from nemo vars to z3 vars for the rule
    pub fn create_var_cache(rule: &NormalizedRule) -> HashMap<Variable, Int> {
        rule.variables()
            .map(|v| {
                (
                    v.clone(),
                    Int::fresh_const(v.name().expect("Anon vars not supported yet")),
                )
            })
            .collect()
    }

    /// Gathers all filter expressions in the program
    pub fn gather_filters(&mut self, program: &NormalizedProgram) {
        let mut filters: Vec<Operation> = Vec::new();
        for rule in program.rules() {
            let rule_filters = rule
                .operations()
                .iter()
                .filter_map(|b| b.get_filter_from_op());
            for filter in rule_filters {
                if !filters
                    .iter()
                    .any(|f: &Operation| f.equivalent_up_to_renaming(&filter))
                {
                    filters.push(filter.clone())
                }
            }
        }
        for annotation in program.global_annotations() {
            let annotation_filters = annotation
                .body()
                .iter()
                .filter_map(|b| b.get_filter_from_op());
            for filter in annotation_filters {
                if !filters
                    .iter()
                    .any(|f: &Operation| f.equivalent_up_to_renaming(&filter))
                {
                    filters.push(filter.clone())
                }
            }
        }
        self.filter_predicates = filters.iter().map(|f| Filter::new(f.clone())).collect();
    }

    /// Returns the restrictions placed on the body predicates
    pub fn get_body_predicate_restrictions(
        &self,
        rule: &NormalizedRule,
        var_cache: &HashMap<Variable, Int>,
    ) -> Vec<Bool> {
        rule.positive()
            .iter()
            .filter_map(|body_atom| {
                self.predicate_restrictions
                    .get(&body_atom.predicate())
                    .and_then(|res| Some(res.get_restrictions_for_body(body_atom, var_cache)))
            })
            .collect()
    }

    /// Verifies a whether a rule satisfies it's annotations
    /// returns true if the annotations could be verified
    pub fn verify_rule(&mut self, program: &NormalizedProgram, rule: &NormalizedRule) -> bool {
        let solver = Solver::new();

        let var_cache = RuleVerifier::create_var_cache(rule);

        let translator = RuleTranslator::new();

        // Translate rule body
        let (body_operations, body_annotations) =
            translator.translate_rule(rule, &var_cache, program);
        for term in body_operations {
            solver.assert(term);
        }

        for term in body_annotations {
            solver.assert(term);
        }

        let mut valid = true;
        let head = &rule.head()[0];

        // Check all annotations for the head
        for head_atom_assertion in program.predicate_to_global_annotation(&head.predicate()) {
            solver.push();
            let head_assertion =
                translator.translate_head_assertion(head_atom_assertion, head, &var_cache);
            solver.assert(&head_assertion.not());
            match solver.check() {
                z3::SatResult::Unsat => {
                    println!("Validated: spec for {head_atom_assertion} holds");
                    valid = valid && true
                }
                z3::SatResult::Unknown => println!("Could not validate (unknown)"),
                z3::SatResult::Sat => {
                    println!(
                        "Rule {} might lead to violation of annotation {}. ",
                        rule, head_atom_assertion
                    );
                    valid = false;
                }
            }
            solver.pop(1);
        }

        valid
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

    /// Print all restrictions
    pub fn print_restriciton(&self) {
        for (tag, restriction) in &self.predicate_restrictions {
            println!("{tag} restriction: {restriction}");
        }
    }

    /// Propagates filter expressions through the program
    pub fn forward_propagation(
        &mut self,
        program: &NormalizedProgram,
        rule: &NormalizedRule,
    ) -> bool {
        let mut delta = false;

        let solver = Solver::new();

        let var_cache = RuleVerifier::create_var_cache(rule);
        let translator = RuleTranslator::new();

        let (body_operations, body_annotations) =
            translator.translate_rule(rule, &var_cache, program);
        for op in body_operations {
            solver.assert(&op);
        }
        for ann in body_annotations {
            solver.assert(&ann);
        }

        let body_restrictions = self.get_body_predicate_restrictions(rule, &var_cache);
        for res in body_restrictions {
            solver.assert(&res);
        }

        let head = &rule.head()[0];

        let mut head_filters: Vec<Bool> = Vec::new();
        for filter in &self.filter_predicates {
            for term in head.terms() {
                solver.push();
                let filter_head = filter.get_filter(&term, &var_cache);
                solver.assert(&filter_head.not());
                match solver.check() {
                    z3::SatResult::Unsat => head_filters.push(filter_head.clone()),
                    _ => {}
                };
                solver.pop(1);
            }
        }

        if !head_filters.is_empty() {
            let head_res = Bool::and(&head_filters);
            self.predicate_restrictions
                .entry(head.predicate())
                .and_modify(|res| {
                    delta =
                        res.add_restriction_from_propagation(head, &var_cache, &head_res) || delta;
                })
                .or_insert_with(|| {
                    //TODO: somehow fix the stuff wiht entailment
                    delta = true;
                    Restriction::new_from_propagation(head, &var_cache, &head_res)
                });
        } else {
            let head_res = Bool::from_bool(true);
            self.predicate_restrictions
                .entry(head.predicate())
                .and_modify(|res| {
                    delta =
                        res.add_restriction_from_propagation(head, &var_cache, &head_res) || delta;
                })
                .or_insert_with(|| {
                    //TODO: somehow fix the stuff wiht entailment
                    delta = true;
                    Restriction::new_from_propagation(head, &var_cache, &head_res)
                });
        }

        delta
    }

    /// Verifies a rule like the function verify_rule, but includes possible propagated restrictions from the rule body
    pub fn verify_with_restrictions(
        &mut self,
        program: &NormalizedProgram,
        rule: &NormalizedRule,
    ) -> bool {
        let solver = Solver::new();

        let var_cache = RuleVerifier::create_var_cache(rule);

        let translator = RuleTranslator::new();

        // Translate rule body
        let (body_operations, body_annotations) =
            translator.translate_rule(rule, &var_cache, program);
        for term in body_operations {
            solver.assert(term);
        }
        for term in body_annotations {
            solver.assert(term);
        }

        let body_restrictions = self.get_body_predicate_restrictions(rule, &var_cache);

        for op in body_restrictions {
            solver.assert(op);
        }

        let mut valid = true;
        let head = &rule.head()[0];

        // Check all annotations for the head
        for head_atom_assertion in program.predicate_to_global_annotation(&head.predicate()) {
            solver.push();
            let head_assertion =
                translator.translate_head_assertion(head_atom_assertion, head, &var_cache);
            solver.assert(&head_assertion.not());
            match solver.check() {
                z3::SatResult::Unsat => {
                    println!("Validated: spec for {head_atom_assertion} holds");
                    valid = valid && true
                }
                z3::SatResult::Unknown => println!("Could not validate (unknown)"),
                z3::SatResult::Sat => {
                    println!(
                        "Rule {} might lead to violation of annotation {}. ",
                        rule, head_atom_assertion
                    );
                    valid = false;
                }
            }
            solver.pop(1);
        }

        valid
    }
}
