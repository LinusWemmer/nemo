//! Gernerates the RuleVerifier of a program
use std::collections::{HashMap, HashSet};

use crate::execution::planning::{
    normalization::{
        atom::ground::GroundAtom,
        global_annotation::NormalizedGlobalAnnotation,
        {program::NormalizedProgram, rule::NormalizedRule},
    },
    verification::rule_verification::{
        z3_goal::VerificationGoal, z3_restriction::Restriction, z3_translation::RuleTranslator,
    },
};

use crate::rule_model::components::{tag::Tag, term::primitive::variable::Variable};

use z3::{
    self, FuncDecl, Sort,
    ast::{Ast, Bool, Int, exists_const},
};
use z3::{Goal, Solver, Tactic};

pub mod z3_goal;
pub mod z3_restriction;
pub mod z3_translation;

/// Struct for converting and verifying rules with z3

#[derive(Debug, Clone)]
pub struct RuleVerifier {
    fresh_var_counter: usize,
    predicate_restrictions: HashMap<Tag, Restriction>,
    /// Arguments that are used in the verification
    verification_goals: HashMap<Tag, VerificationGoal>,
}

impl RuleVerifier {
    /// Creates a new [RuleVerifier]
    pub fn new() -> Self {
        Self {
            fresh_var_counter: 0,
            predicate_restrictions: HashMap::new(),
            verification_goals: HashMap::new(),
        }
    }

    /// Generates a new var for the program
    pub fn get_fresh_var(&mut self) -> String {
        self.fresh_var_counter += 1;
        format!("V{}", self.fresh_var_counter)
    }

    /// Returns the verification goals
    pub fn verification_goals(&self) -> &HashMap<Tag, VerificationGoal> {
        &self.verification_goals
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

    /// Add predicate restrictions from input annotation
    /// #Panics
    ///  * panics when there are two input annotations for the same predicate
    /*pub fn add_restriction_from_input_annotation(&mut self, annotation: &NormalizedInputAnnotation) {
        if let Some(_) = self.predicate_restrictions.insert(
            annotation.head().predicate(),
            Restriction::new_from_annotation(annotation),
        ) {
            panic!("Only one input annotation should be used per predicate")
        }
    }*/

    /// Add verification goal from output predicate
    pub fn add_output_verification_goal(&mut self, annotation: &NormalizedGlobalAnnotation) {
        let goal = VerificationGoal::new_from_annotation(annotation);
        self.verification_goals
            .insert(annotation.head().predicate(), goal);
    }

    /// Propagates head goals to body, logical and them, sort of like weakest precondition
    /// Returns all predicates for that new goals were generated
    pub fn backward_prop_goals(&mut self, predicate: &Tag, rule: &NormalizedRule) -> HashSet<Tag> {
        if let Some(head_verification_goal) = self.verification_goals.get(predicate) {
            let translator = RuleTranslator::new();
            let tactic_qe = Tactic::new("qe");

            let var_cache = RuleVerifier::create_var_cache(rule);

            let mut body_operations: Vec<Bool> = rule
                .operations()
                .iter()
                .map(|b| {
                    translator
                        .translate_operation(b, &var_cache)
                        .as_bool()
                        .expect("Top level operations should have Sort Bool")
                })
                .collect();

            let head_goal =
                Bool::and(&head_verification_goal.goal_from_head_atom(&rule.head()[0], &var_cache))
                    .not();
            // TODO: maybe with implication instead of conjuncition
            body_operations.push(head_goal);

            let mut added_goals = HashSet::new();
            // Over approximation by eliminating variables ( eg. x= y +z, x>0, if y and z are in different predicates, information is lost)
            // as we only keep goals on a per predicate basis, sort of weakest precondition
            for body_atom in rule.positive() {
                let goal = Goal::new(false, false, false);
                let atom_vars_set: HashSet<&Variable> = body_atom.terms().collect();
                let rule_vars: HashSet<&Variable> = rule.variables().collect();
                let args: Vec<&dyn Ast> = rule_vars
                    .difference(&atom_vars_set)
                    .map(|v| var_cache.get(v).expect("variable should be registered"))
                    .map(|v| -> &dyn Ast { v })
                    .collect();
                goal.assert(&exists_const(&args, &[], &Bool::and(&body_operations)));
                let result = tactic_qe
                    .apply(&goal, None)
                    .expect("qe tactic failed")
                    .list_subgoals()
                    .collect::<Vec<Goal>>();
                if let Some(goal) = result.first() {
                    let filters = goal.get_formulas();
                    if !filters.is_empty() {
                        // Note: might yield vacuous statements from guards in rule, i.e. goals that would mean the rule doesn't fire
                        let new_goal: Bool;
                        if filters.len() == 1 {
                            new_goal = filters.first().expect("").not();
                        } else {
                            new_goal = Bool::and(&filters).not();
                        }
                        self.verification_goals
                            .entry(body_atom.predicate())
                            .and_modify(|g| g.add_propagated_goal(body_atom, &var_cache, &new_goal))
                            .or_insert(VerificationGoal::new_from_propagation(
                                body_atom, &var_cache, &new_goal,
                            ));
                        added_goals.insert(body_atom.predicate());
                    }

                    // add to z3_goal from prop
                }
            }
            return added_goals;
        }
        HashSet::new()
    }

    /// Verifies a whether a rule satisfies it's annotations
    /// returns true if the annotations could be verified
    pub fn verify_rule(&mut self, program: &NormalizedProgram, rule: &NormalizedRule) -> bool {
        let solver = Solver::new();

        let var_cache = RuleVerifier::create_var_cache(rule);

        let translator = RuleTranslator::new();

        // Translate rule body
        let body_instance = translator.translate_rule(rule, &var_cache, program);
        for term in body_instance {
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
                    println!(
                        "Rule {} might lead to violation of {} with var assigment {}. ",
                        rule, head_atom_assertion, var_interpretation
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

    /// Checks whether the goal has been proven at least once and never been refuted
    pub fn check_goal_state(&self, predicate: &Tag) -> bool {
        if let Some(goal) = self.verification_goals.get(predicate) {
            return goal.is_proven();
        }
        true
    }

    /// Propagates filters atoms from rule body to head, returns true if new info was gained
    /// Doesn't  support input annotation at this point
    pub fn verify_with_propagation(
        &mut self,
        program: &NormalizedProgram,
        rule: &NormalizedRule,
    ) -> bool {
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
        let var_cache = RuleVerifier::create_var_cache(rule);

        let translator = RuleTranslator::new_with_predicates(predicate_to_z3_fun);

        // Translate rule body TODO: split up annotation and other thing in body
        let body_instance = translator.translate_rule(rule, &var_cache, program);
        for term in body_instance {
            solver.assert(term);
        }

        let proven_body_goals = rule
            .positive()
            .iter()
            .filter_map(|b| {
                self.verification_goals
                    .get(&b.predicate())
                    .and_then(|g| match g.is_proven() {
                        true => Some(g.goal_from_body_atom(&b, &var_cache)),
                        false => None,
                    })
            })
            .flatten();

        for g in proven_body_goals {
            solver.assert(&g);
        }

        let mut delta = false;
        // TODO: check if rule could fire before checking, otherwise goal gets set to true without verification
        let head = &rule.head()[0];
        if let Some(verification_goal) = self.verification_goals.get_mut(&head.predicate()) {
            if !verification_goal.is_refuted() {
                solver.push();
                let proof_goal = verification_goal.goal_from_head_atom(&head, &var_cache);
                solver.assert(&Bool::and(&proof_goal).not());
                match solver.check() {
                    z3::SatResult::Unsat => delta = verification_goal.goal_proven() || delta,
                    z3::SatResult::Unknown => println!("Could not validate (unknown)"),
                    z3::SatResult::Sat => delta = verification_goal.goal_refuted() || delta,
                }
                solver.pop(1);
            }
        }

        // check all annotations
        for head_atom_assertion in program.predicate_to_global_annotation(&head.predicate()) {
            solver.push();
            let head_assertion =
                translator.translate_head_assertion(head_atom_assertion, head, &var_cache);
            solver.assert(&head_assertion.not());
            match solver.check() {
                z3::SatResult::Unsat => println!("Validated: spec for {head_atom_assertion} holds"),
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
                    println!(
                        "Rule {} might lead to violation of {} with var assigment {}, ",
                        rule, head_atom_assertion, var_interpretation
                    );
                }
            }
            solver.pop(1);
        }

        delta
    }

    /// verifies a rule and propagates restriction from the body to the head
    pub fn forward_propagation(&mut self, program: &NormalizedProgram, rule: &NormalizedRule) {
        let goal = Goal::new(false, false, false);
        let tactic_qe = Tactic::new("qe");

        let translator = RuleTranslator::new();
        let var_cache = RuleVerifier::create_var_cache(rule);

        // Translate rule body
        let mut body_instance = translator.translate_rule(rule, &var_cache, program);
        let body_restrictions = rule.positive().iter().filter_map(|body_atom| {
            self.predicate_restrictions
                .get(&body_atom.predicate())
                .and_then(|res| Some(res.get_restrictions_for_body(body_atom, &var_cache)))
        });
        body_instance.extend(body_restrictions);

        let head = &rule.head()[0];

        let rule_variables: HashSet<&Variable> = rule.variables().collect();
        let head_variables: HashSet<&Variable> = head.variables().collect();
        let args: Vec<&dyn Ast> = rule_variables
            .difference(&head_variables)
            .map(|v| var_cache.get(v).expect("variable should be registered"))
            .map(|v| -> &dyn Ast { v })
            .collect();

        goal.assert(&exists_const(&args, &[], &Bool::and(&body_instance)));
        let result = tactic_qe
            .apply(&goal, None)
            .expect("qe tactic failed")
            .list_subgoals()
            .collect::<Vec<Goal>>();

        if let Some(goal) = result.first() {
            let new_restriction = goal.get_formulas();
            if !new_restriction.is_empty() {
                let head_res: Bool;
                if new_restriction.len() == 1 {
                    head_res = new_restriction.first().expect("").clone();
                } else {
                    head_res = Bool::and(&new_restriction);
                }
                self.predicate_restrictions
                    .entry(head.predicate())
                    .and_modify(|res| {
                        res.add_restriction_from_propagation(head, &var_cache, &head_res);
                    })
                    .or_insert(Restriction::new_from_propagation(
                        head, &var_cache, &head_res,
                    ));
            }
        }
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
        let body_instance = translator.translate_rule(rule, &var_cache, program);
        for term in body_instance {
            solver.assert(term);
        }

        let body_restrictions = rule.positive().iter().filter_map(|body_atom| {
            self.predicate_restrictions
                .get(&body_atom.predicate())
                .and_then(|res| {
                    println!("{body_atom} restriction: {res}");
                    Some(res.get_restrictions_for_body(body_atom, &var_cache))
                })
        });
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
                    println!(
                        "Rule {} might lead to violation of {} with var assigment {}. ",
                        rule, head_atom_assertion, var_interpretation
                    );
                    valid = false;
                }
            }
            solver.pop(1);
        }

        valid
    }
}
