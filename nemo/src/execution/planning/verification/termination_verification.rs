//! This module defines [TerminationVerifier]

use std::collections::{HashMap, HashSet};

use z3::{
    Solver,
    ast::{Ast, Bool, Int, forall_const},
};

use crate::{
    execution::planning::{
        normalization::{
            program::NormalizedProgram, rule::NormalizedRule,
            termination_annotation::NormalizedTerminationAnnotation,
            termination_annotation::TerminationDirection,
        },
        verification::{
            annotation_analysis::propagation_graph::PropagationGraph,
            edb_analysis::EdbAnalyzer,
            rule_verification::{
                RuleVerifier, z3_restriction::Restriction, z3_translation::RuleTranslator,
            },
        },
    },
    rule_model::components::{
        tag::Tag,
        term::primitive::{Primitive, variable::Variable},
    },
};

/// Checks whether the program terminates
#[derive(Debug, Clone)]
pub struct TerminationVerifier {
    edb_predicates: EdbAnalyzer,
    _predicate_restrictions: HashMap<Tag, Restriction>,
}

impl TerminationVerifier {
    /// Create a new [RuleVerifier]
    pub fn new(
        edb_predicates: EdbAnalyzer,
        _predicate_restrictions: HashMap<Tag, Restriction>,
    ) -> Self {
        Self {
            edb_predicates,
            _predicate_restrictions,
        }
    }
}

impl TerminationVerifier {
    /// Constructs a map from nemo variables to z3 variables
    pub fn build_var_cache(&self, rule: &NormalizedRule, i: usize) -> HashMap<Variable, Int> {
        rule.variables()
            .map(|v| {
                let name = format!("{}{i}", v.name().expect("Anon vars not supported yet"));
                (v.clone(), Int::fresh_const(&name))
            })
            .collect()
    }

    /// Prints a rule cycle, TODO: make pretty
    pub fn print_cycle(cycle: &Vec<&NormalizedRule>) {
        print!("(");
        for rule in cycle {
            print!("{rule}, ")
        }
        println!(")")
    }

    /// Generates the unfolded representation of the loop
    /// Returns in order:
    /// * The expressions used in the unfolded loop in smtlib rep
    /// * The recursive predicate in the start of the cycle
    /// * The recursive vars at the end of the cycle
    pub fn compose_cycle(
        &self,
        cycle: &Vec<&NormalizedRule>,
        annotation: &NormalizedTerminationAnnotation,
        incremental_predicate: &Tag,
    ) -> (Vec<Bool>, Vec<Int>, Int, HashSet<Int>, HashSet<Int>) {
        let translator = RuleTranslator::new();
        let size = cycle.len();

        let mut current_rule = cycle[0];
        let mut var_cache_previous: HashMap<Variable, Int> = self.build_var_cache(current_rule, 0);

        let mut edb_vars = self.edb_vars_in_rule(current_rule, &var_cache_previous);
        let mut cycle_vars: HashSet<Int> = current_rule
            .variables()
            .map(|v| var_cache_previous.get(v).expect("var should exist").clone())
            .collect();

        let cycle_start_norm = current_rule
            .positive()
            .iter()
            .filter(|b| b.predicate() == *incremental_predicate)
            .map(|b| {
                translator.translate_termination_annotation_body(annotation, b, &var_cache_previous)
            })
            .collect();

        //TODO: add back in support for annotation or at least restrictions
        let mut previous_rule_translation = translator
            .translate_rule_operations_without_annotations(&current_rule, &var_cache_previous);
        let previous_head = &current_rule.head()[0];

        for c_i in 1..size {
            current_rule = cycle[c_i];
            let var_cache_current: HashMap<Variable, Int> = self.build_var_cache(current_rule, c_i);
            let mut current_rule_translation = translator
                .translate_rule_operations_without_annotations(&current_rule, &var_cache_current);
            //TODO: joins have to be handled more carefully
            for previous_head_occurence in current_rule
                .positive()
                .iter()
                .filter(|b| b.predicate() == previous_head.predicate())
            {
                let substitution: Vec<(&Int, &Int)> = previous_head
                    .terms()
                    .zip(previous_head_occurence.terms())
                    .filter_map(|(prev, cur)| match prev {
                        Primitive::Variable(v) => Some((
                            var_cache_previous.get(v).expect("msg"),
                            var_cache_current.get(cur).expect("should exist"),
                        )),
                        Primitive::Ground(_) => None,
                    })
                    .collect();

                //TODO: check upper /lower boudn: also x<edb
                current_rule_translation.extend(
                    previous_rule_translation
                        .iter()
                        .map(|f| f.substitute(&substitution)),
                );
                edb_vars = edb_vars
                    .iter()
                    .map(|v| v.substitute(&substitution))
                    .collect();
                edb_vars.extend(self.edb_vars_in_rule(current_rule, &var_cache_current));

                cycle_vars = cycle_vars
                    .iter()
                    .map(|v| v.substitute(&substitution))
                    .collect();
                cycle_vars.extend(
                    current_rule
                        .variables()
                        .map(|v| var_cache_previous.get(v).expect("var should exist").clone()),
                );

                var_cache_previous = var_cache_current.clone();
                previous_rule_translation = current_rule_translation.clone();
            }
        }

        let cycle_end_norm = translator
            .translate_termination_annotation_head(
                annotation,
                &current_rule.head()[0],
                &var_cache_previous,
            )
            .clone();

        (
            previous_rule_translation,
            cycle_start_norm,
            cycle_end_norm,
            edb_vars,
            cycle_vars,
        )
    }

    // How to check bound vars:
    // Each one that is bound in previous rule is bound
    // TODO: vars that only depend on bound vars are also bound
    // it might be possible to do this with a boundedness check using z3?
    /// Returns all bound vars for the rule
    pub fn edb_vars_in_rule(
        &self,
        rule: &NormalizedRule,
        var_cache: &HashMap<Variable, Int>,
    ) -> HashSet<Int> {
        let edb_variables: HashSet<Variable> = self.edb_predicates.bound_vars_in_rule(rule);
        edb_variables
            .iter()
            .map(|v| var_cache.get(v).expect("var should exist").clone())
            .collect()
    }
    /// Checks if the the argument position increases (unknown returns false)
    pub fn strictly_changes_argument(
        &self,
        composed_cycle: &Vec<Bool>,
        cycle_start_norm: &Vec<Int>,
        cycle_end_norm: &Int,
        annotation: &NormalizedTerminationAnnotation,
    ) -> bool {
        let solver = Solver::new();

        for statement in composed_cycle {
            solver.assert(statement);
        }
        let mut valid = true;
        match annotation.direction() {
            TerminationDirection::Decreasing => {
                for starting_norm in cycle_start_norm {
                    solver.push();
                    solver.assert(starting_norm.gt(cycle_end_norm).not());
                    println!("{}", solver.to_smt2());
                    valid = valid
                        && match solver.check() {
                            z3::SatResult::Unsat => true,
                            z3::SatResult::Unknown => {
                                println!("Could not validate (unknown)");
                                return false;
                            }
                            z3::SatResult::Sat => false,
                        };
                    solver.pop(1);
                }
            }
            TerminationDirection::Increasing => {
                for starting_norm in cycle_start_norm {
                    solver.push();
                    solver.assert(starting_norm.lt(cycle_end_norm).not());
                    println!("{}", solver.to_smt2());
                    valid = valid
                        && match solver.check() {
                            z3::SatResult::Unsat => true,
                            z3::SatResult::Unknown => {
                                println!("Could not validate (unknown)");
                                return false;
                            }
                            z3::SatResult::Sat => false,
                        };
                    solver.pop(1);
                }
            }
        }
        valid
    }

    /// Checks if the the argument position increases (unknown returns false)
    pub fn decreases_argument(
        &self,
        rule: &NormalizedRule,
        head_pos: usize,
        body_predicate: &Tag,
        body_pos: usize,
        program: &NormalizedProgram,
    ) -> bool {
        let solver = Solver::new();
        let var_cache = RuleVerifier::create_var_cache(rule);
        let translator = RuleTranslator::new();

        let body_instance = translator.translate_rule(rule, &var_cache, program);
        for term in body_instance {
            solver.assert(term);
        }

        let head_term = translator.translate_primitive(
            rule.head()[0]
                .terms()
                .nth(head_pos)
                .expect("there should be a term in head_atom"),
            &var_cache,
        );

        rule.positive()
            .iter()
            .filter(|b| b.predicate() == *body_predicate)
            .for_each(|b| {
                let var = var_cache
                    .get(&b.terms().nth(body_pos).expect("var should exist"))
                    .expect("var should exist");
                let increasing = head_term.lt(var);
                solver.assert(&increasing.not());
            });

        match solver.check() {
            z3::SatResult::Unsat => true,
            z3::SatResult::Unknown => {
                println!("Could not validate (unknown)");
                return false;
            }
            z3::SatResult::Sat => false,
        }
    }

    /// Checks whether the cycle has an upper bound
    pub fn expression_has_upper_bound(
        &self,
        edb_vars: &HashSet<Int>,
        composed_cycle: &Vec<Bool>,
        cycle_vars: &HashSet<Int>,
        norm: &Int,
    ) -> bool {
        let solver = Solver::new();
        let hi = Int::fresh_const("hi");
        //let lo = Int::fresh_const("lo");
        let mut lhs = Vec::new();
        for var in edb_vars {
            let hi_edb = Int::fresh_const("hi_edb");
            let lo_edb = Int::fresh_const("lo_edb");
            lhs.push(lo_edb.le(var));
            lhs.push(var.le(hi_edb));
        }
        lhs.extend(composed_cycle.iter().cloned());
        let lhs_combined = Bool::and(&lhs);
        let rhs = norm.le(hi);
        let implies = lhs_combined.implies(rhs);
        let args: Vec<&dyn Ast> = cycle_vars.iter().map(|v| -> &dyn Ast { v }).collect();
        let formula = forall_const(&args, &[], &implies);
        solver.assert(formula);
        println!("{}", solver.to_smt2());
        match solver.check() {
            z3::SatResult::Unsat => false,
            z3::SatResult::Unknown => {
                println!("Could not validate (unknown)");
                return false;
            }
            z3::SatResult::Sat => true,
        }
    }

    /// Checks whether the cycle has an upper bound
    pub fn expression_has_lower_bound(
        &self,
        edb_vars: &HashSet<Int>,
        composed_cycle: &Vec<Bool>,
        cycle_vars: &HashSet<Int>,
        norm: &Int,
    ) -> bool {
        let solver = Solver::new();
        let lo = Int::fresh_const("lo");
        //let lo = Int::fresh_const("lo");
        let mut lhs = Vec::new();
        for var in edb_vars {
            let hi_edb = Int::fresh_const("hi_edb");
            let lo_edb = Int::fresh_const("lo_edb");
            lhs.push(lo_edb.le(var));
            lhs.push(var.le(hi_edb));
        }
        lhs.extend(composed_cycle.iter().cloned());
        let lhs_combined = Bool::and(&lhs);
        let rhs = norm.ge(lo);
        let implies = lhs_combined.implies(rhs);
        let args: Vec<&dyn Ast> = cycle_vars.iter().map(|v| -> &dyn Ast { v }).collect();
        let formula = forall_const(&args, &[], &implies);
        solver.assert(formula);
        println!("{}", solver.to_smt2());
        match solver.check() {
            z3::SatResult::Unsat => false,
            z3::SatResult::Unknown => {
                println!("Could not validate (unknown)");
                return false;
            }
            z3::SatResult::Sat => true,
        }
    }

    /// Checks if the permutated cycle terminates by the given termination annotation
    pub fn cycle_terminates_by_annotation(
        &self,
        cycle: &Vec<&NormalizedRule>,
        annotation: &NormalizedTerminationAnnotation,
        cycle_predicate: &Tag,
    ) -> bool {
        let (composed_cycle, cycle_start_norm, cycle_end_norm, edb_vars, cycle_vars) =
            self.compose_cycle(cycle, annotation, cycle_predicate);
        if self.strictly_changes_argument(
            &composed_cycle,
            &cycle_start_norm,
            &cycle_end_norm,
            annotation,
        ) {
            println!("cycle strictly changes");
            // Check bound
            let has_bound = match annotation.direction() {
                TerminationDirection::Decreasing => self.expression_has_lower_bound(
                    &edb_vars,
                    &composed_cycle,
                    &cycle_vars,
                    &cycle_end_norm,
                ),
                TerminationDirection::Increasing => self.expression_has_upper_bound(
                    &edb_vars,
                    &composed_cycle,
                    &cycle_vars,
                    &cycle_end_norm,
                ),
            };
            has_bound
        } else {
            false
        }
    }

    /// Check whether for any permutation of a cycle with a fitting annotation, termination can be proven
    pub fn check_all_annotated_cycle_permutations(
        &self,
        rule_cycle: &Vec<&NormalizedRule>,
        program: &NormalizedProgram,
    ) -> bool {
        let cycle_len = rule_cycle.len();
        let potential_starts: Vec<usize> = rule_cycle
            .iter()
            .enumerate()
            .filter(|(_, rule)| {
                program.has_termination_annotation_predicate(&rule.head()[0].predicate())
            })
            .map(|(p, _)| p)
            .collect();

        for start in potential_starts {
            let permutated_cycle: Vec<&NormalizedRule> = rule_cycle
                .iter()
                .cycle()
                .skip(start)
                .take(cycle_len)
                .cloned()
                .collect();

            let cycle_predicate = &permutated_cycle[0].head()[0].predicate();
            let annotation = program.predicate_to_termination_annotation(cycle_predicate)[0];
            let terminates_by_annotation =
                self.cycle_terminates_by_annotation(&permutated_cycle, annotation, cycle_predicate);
            if terminates_by_annotation {
                print!("Termination for cycle ");
                TerminationVerifier::print_cycle(&permutated_cycle);
                println!("could be verified with annotation {annotation}.");
                return true;
            }
        }
        false
    }

    /// Checks all cycles for the scc
    pub fn check_scc_cycles(&self, program: &NormalizedProgram, scc: &Vec<usize>) -> bool {
        let propagation_graph = PropagationGraph::build_graph(&scc, program.rules());
        if propagation_graph.is_weakly_acyclic() {
            println!("weakly acyclic");
            return true;
        } else {
            println!("not weakly acyclic");
            let cycles = propagation_graph.all_special_rules_cycles();
            println!("{:?}", cycles);
            for cycle in cycles {
                let rule_cycle: Vec<&NormalizedRule> =
                    cycle.iter().map(|r_i| &program.rules()[*r_i]).collect();
                let termination_proven =
                    self.check_all_annotated_cycle_permutations(&rule_cycle, program);

                if !termination_proven {
                    print!("Termination for cycle: ");
                    // TODO: make pretty
                    println!("{:?}", cycle);
                    println!(
                        "could not be verified. Consider adding annotations if you believe the cycle terminates"
                    );
                }
            }
            true
        }
    }
}
