//! This module defines [TerminationVerifier]

use std::{
    collections::{HashMap, HashSet},
    i64,
};

use z3::{
    Optimize, Solver,
    ast::{Ast, Bool, Int},
};

use crate::{
    execution::planning::{
        normalization::{
            program::NormalizedProgram,
            rule::NormalizedRule,
            termination_annotation::{NormalizedTerminationAnnotation, TerminationDirection},
        },
        verification::{
            annotation_analysis::propagation_graph::PropagationGraph,
            edb_analysis::EdbAnalyzer,
            rule_verification::{z3_restriction::Restriction, z3_translation::RuleTranslator},
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
    program: NormalizedProgram,
}

impl TerminationVerifier {
    /// Create a new [RuleVerifier]
    pub fn new(
        edb_predicates: EdbAnalyzer,
        _predicate_restrictions: HashMap<Tag, Restriction>,
        program: NormalizedProgram,
    ) -> Self {
        Self {
            edb_predicates,
            _predicate_restrictions,
            program,
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
    /// TODO: restriction
    /// TODO: incorporate joins if some predicate appears multiple times in body
    pub fn compose_cycle(
        &self,
        cycle: &Vec<&NormalizedRule>,
        annotation: &NormalizedTerminationAnnotation,
        incremental_predicate: &Tag,
    ) -> (Vec<Bool>, Vec<Int>, Int, HashSet<Int>) {
        let translator = RuleTranslator::new();
        let size = cycle.len();

        let mut current_rule = cycle[0];
        let mut var_cache_previous: HashMap<Variable, Int> = self.build_var_cache(current_rule, 0);

        let mut edb_vars = self.edb_vars_in_rule(current_rule, &var_cache_previous);

        let mut cycle_start_norm: Vec<Int> = current_rule
            .positive()
            .iter()
            .filter(|b| b.predicate() == *incremental_predicate)
            .map(|b| {
                translator.translate_termination_annotation_body(annotation, b, &var_cache_previous)
            })
            .collect();

        //TODO: add back in support for restrictions
        let mut complete_rule_translation: Vec<Bool> = Vec::new();

        let (previous_rule_body, previous_rule_annotations) =
            translator.translate_rule(&current_rule, &var_cache_previous, &self.program);
        complete_rule_translation.extend(previous_rule_body);
        complete_rule_translation.extend(previous_rule_annotations);
        let mut previous_head = &current_rule.head()[0];

        for c_i in 1..size {
            current_rule = cycle[c_i];
            let var_cache_current: HashMap<Variable, Int> = self.build_var_cache(current_rule, c_i);

            let (current_rule_body, current_rule_annotations) =
                translator.translate_rule(&current_rule, &var_cache_current, &self.program);
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

                cycle_start_norm = cycle_start_norm
                    .iter()
                    .map(|n| n.substitute(&substitution))
                    .collect();
                complete_rule_translation = complete_rule_translation
                    .iter()
                    .map(|f| f.substitute(&substitution))
                    .collect();

                complete_rule_translation.extend(current_rule_body.clone());
                complete_rule_translation.extend(current_rule_annotations.clone());

                edb_vars = edb_vars
                    .iter()
                    .map(|v| v.substitute(&substitution))
                    .collect();
                edb_vars.extend(self.edb_vars_in_rule(current_rule, &var_cache_current));

                var_cache_previous = var_cache_current.clone();
                previous_head = &current_rule.head()[0];
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
            complete_rule_translation,
            cycle_start_norm,
            cycle_end_norm,
            edb_vars,
        )
    }

    // How to check bound vars:
    // Each one that is bound in previous rule is bound
    // it might be possible to do this with a boundedness check using z3?
    /// Returns all bound vars for the rule
    pub fn edb_vars_in_rule(
        &self,
        rule: &NormalizedRule,
        var_cache: &HashMap<Variable, Int>,
    ) -> HashSet<Int> {
        let edb_variables: HashSet<Variable> = self.edb_predicates.edb_vars_in_rule(rule);
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

    /// Checks whether the cycle has an upper bound
    pub fn expression_has_upper_bound(
        &self,
        composed_cycle: &Vec<Bool>,
        norm: &Int,
        edb_vars: &HashSet<Int>,
    ) -> bool {
        let optimize = Optimize::new();
        let int_max = i64::MAX;
        let int_min = i64::MIN;
        for var in edb_vars {
            optimize.assert(var.lt(int_max));
            optimize.assert(var.gt(int_min));
        }
        for term in composed_cycle {
            optimize.assert(term);
        }
        optimize.maximize(norm);
        optimize.check(&[]);

        match optimize.get_upper(0) {
            Some(a) => {
                return !a.to_string().contains("oo");
            }
            None => false,
        }
    }

    /// Checks whether the cycle has a lower bound
    pub fn expression_has_lower_bound(
        &self,
        composed_cycle: &Vec<Bool>,
        norm: &Int,
        edb_vars: &HashSet<Int>,
    ) -> bool {
        let optimize = Optimize::new();
        let int_max = i64::MAX;
        let int_min = i64::MIN;
        for var in edb_vars {
            optimize.assert(var.lt(int_max));
            optimize.assert(var.gt(int_min));
        }
        for term in composed_cycle {
            optimize.assert(term);
        }
        optimize.minimize(norm);
        optimize.check(&[]);

        match optimize.get_lower(0) {
            Some(a) => {
                return !a.to_string().contains("oo");
            }
            None => false,
        }
    }

    /// Checks if the permutated cycle terminates by the given termination annotation
    pub fn cycle_terminates_by_annotation(
        &self,
        cycle: &Vec<&NormalizedRule>,
        annotation: &NormalizedTerminationAnnotation,
        cycle_predicate: &Tag,
    ) -> bool {
        let (composed_cycle, cycle_start_norm, cycle_end_norm, edb_vars) =
            self.compose_cycle(cycle, annotation, cycle_predicate);
        if self.strictly_changes_argument(
            &composed_cycle,
            &cycle_start_norm,
            &cycle_end_norm,
            annotation,
        ) {
            println!("cycle strictly changes");
            // Check bound TODO: incorporate bound by rules
            let has_bound = match annotation.direction() {
                TerminationDirection::Decreasing => {
                    self.expression_has_lower_bound(&composed_cycle, &cycle_end_norm, &edb_vars)
                }
                TerminationDirection::Increasing => {
                    self.expression_has_upper_bound(&composed_cycle, &cycle_end_norm, &edb_vars)
                }
            };
            has_bound
        } else {
            false
        }
    }

    /// Checks whether the analyzed scc is single predicate dependent, and the corresponding cycle pred
    pub fn single_predicate_dependent(&self, cycles: &Vec<Vec<usize>>) -> Option<Tag> {
        let mut counts: HashMap<usize, usize> = HashMap::new();
        for cycle in cycles {
            for rule_index in cycle {
                *counts.entry(*rule_index).or_insert(0) += 1;
            }
        }
        let intersect_preds: Vec<Tag> = counts
            .iter()
            .filter(|(_, count)| **count >= 2)
            .map(|(index, _)| self.program.rules()[*index].head()[0].predicate())
            .collect();
        if intersect_preds.len() == 1 {
            println!("spp!");
            Some(intersect_preds[0].clone())
        } else {
            None
        }
    }

    /// Checks whether termination can be verified with the given cycle predicate
    pub fn check_cycle_termination_with_predicate(
        &self,
        rule_cycle: &Vec<&NormalizedRule>,
        cycle_predicate: &Tag,
    ) -> bool {
        let cycle_len = rule_cycle.len();
        println!("{cycle_predicate}");
        if self
            .program
            .predicate_has_termination_annotation(cycle_predicate)
        {
            let potential_starts: Vec<usize> = rule_cycle
                .iter()
                .enumerate()
                .filter(|(_, rule)| rule.head()[0].predicate() == *cycle_predicate)
                .map(|(p, _)| p)
                .collect();
            for start in potential_starts {
                let permutated_cycle: Vec<&NormalizedRule> = rule_cycle
                    .iter()
                    .cycle()
                    .skip(start + 1)
                    .take(cycle_len)
                    .cloned()
                    .collect();
                let annotation = self
                    .program
                    .predicate_to_termination_annotation(cycle_predicate)[0];
                let terminates_by_annotation = self.cycle_terminates_by_annotation(
                    &permutated_cycle,
                    annotation,
                    cycle_predicate,
                );
                if terminates_by_annotation {
                    print!("Termination for cycle ");
                    TerminationVerifier::print_cycle(&permutated_cycle);
                    println!("could be verified with annotation {annotation}.");
                    return true;
                }
            }
        }
        false
    }

    /// Check whether for any permutation of a cycle with a fitting annotation, termination can be proven
    pub fn check_all_cycle_permutations(&self, rule_cycle: &Vec<&NormalizedRule>) -> bool {
        let cycle_len = rule_cycle.len();
        let potential_starts: Vec<usize> = rule_cycle
            .iter()
            .enumerate()
            .filter(|(_, rule)| {
                self.program
                    .predicate_has_termination_annotation(&rule.head()[0].predicate())
            })
            .map(|(p, _)| p)
            .collect();

        for start in potential_starts {
            let permutated_cycle: Vec<&NormalizedRule> = rule_cycle
                .iter()
                .cycle()
                .skip(start + 1)
                .take(cycle_len)
                .cloned()
                .collect();

            let cycle_predicate = &permutated_cycle
                .last()
                .expect("there should be a last element in cycle")
                .head()[0]
                .predicate();
            let annotation = self
                .program
                .predicate_to_termination_annotation(cycle_predicate)[0];
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
    pub fn check_scc_termination(&self, scc: &Vec<usize>) -> bool {
        let propagation_graph = PropagationGraph::build_graph(&self.program, &scc);
        if propagation_graph.is_weakly_acyclic() {
            println!("weakly acyclic");
            return true;
        } else {
            println!("not weakly acyclic");
            //TODO: implement property
            let cycles = propagation_graph.all_rule_cycles();

            //check single cycle dependency if there are multiple cycles in the scc
            //TODO: what happens if this fails
            if cycles.len() > 1
                && let Some(t_pred) = self.single_predicate_dependent(&cycles)
            {
                println!("cycle predicate: {t_pred}");
                for cycle in cycles {
                    let rule_cycle: Vec<&NormalizedRule> = cycle
                        .iter()
                        .map(|r_i| &self.program.rules()[*r_i])
                        .collect();
                    println!("checking cycle: {:?}", cycle);
                    let termination_proven =
                        self.check_cycle_termination_with_predicate(&rule_cycle, &t_pred);

                    if !termination_proven {
                        print!("Termination for cycle: ");
                        // TODO: make pretty
                        TerminationVerifier::print_cycle(&rule_cycle);
                        println!(
                            "could not be verified. Consider adding annotations if you believe the cycle terminates"
                        );
                    }
                }
            } else if cycles.len() == 1 {
                let cycle = &cycles[0];
                let rule_cycle: Vec<&NormalizedRule> = cycle
                    .iter()
                    .map(|r_i| &self.program.rules()[*r_i])
                    .collect();
                println!("checking cycle: {:?}", cycle);
                let termination_proven = self.check_all_cycle_permutations(&rule_cycle);

                if !termination_proven {
                    print!("Termination for cycle: ");
                    // TODO: make pretty
                    TerminationVerifier::print_cycle(&rule_cycle);
                    println!(
                        "could not be verified. Consider adding annotations if you believe the cycle terminates"
                    );
                }
            }
            true
        }
    }
}
