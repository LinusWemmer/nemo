//! This Module Defines define [AnnotationAnalyzer]

use std::collections::HashSet;

use crate::{
    execution::{
        planning::{
            normalization::{
                global_annotation::NormalizedGlobalAnnotation, program::NormalizedProgram,
                rule::NormalizedRule,
            },
            verification::{
                annotation_analysis::{
                    propagation_graph::PropagationGraph, rule_selection::RuleAnalysisGraph,
                },
                rule_verification::RuleVerifier,
            },
        },
        selection_strategy::dependency_graph::graph_positive::GraphConstructorPositive,
    },
    rule_model::components::tag::Tag,
};

//pub mod analysis_report;
pub mod propagation_graph;
pub mod rule_selection;

/// Analyzes the given annotations
#[derive(Debug, Default, Clone)]
pub struct AnnotationAnalyzer {
    /// The program to be analized
    program: NormalizedProgram,
    // The Set of Restrictions on the predicate with respective arity
    //unary_restrictions: HashMap<(Tag, usize), RangeRestriction>,
}

impl AnnotationAnalyzer {
    /// Create a new [AnnotationAnalyzer]
    pub fn new(program: &NormalizedProgram) -> Self {
        let program = program.clone();
        Self {
            program,
            //unary_restrictions: HashMap::default(),
        }
    }

    /// Return the underlying program
    pub fn program(&self) -> &NormalizedProgram {
        &self.program
    }
}

impl AnnotationAnalyzer {
    /// Gets the annotations for all edb predicates in the program
    pub fn edb_annotations(
        program: &NormalizedProgram,
    ) -> impl Iterator<Item = &NormalizedGlobalAnnotation> {
        let derived = program.derived_predicates();

        program.global_annotations().iter().filter(|annotation| {
            !derived.contains(&NormalizedGlobalAnnotation::head(annotation).predicate())
        })
    }

    /// Verifies annotations of a program whether they all "support" each other without contradiction
    /// No propagation is done, so most annotations have to be written by user
    pub fn verify_annotations(&mut self) {
        let mut verifier = RuleVerifier::new();

        for fact in self.program.facts() {
            verifier.verify_facts(fact, self.program());
        }

        let mut rule_graph = RuleAnalysisGraph::<GraphConstructorPositive>::new(
            self.program.rules().iter().collect(),
        );

        let mut valid = true;

        // actually not really necessary
        while let Some(scc) = rule_graph.next_scc() {
            for rule_index in &scc {
                let rule = &self.program.rules()[*rule_index];
                println!("Checking rule {rule_index}: {rule}");
                valid = verifier.verify_rule(self.program(), rule) && valid;
            }
        }
        if valid {
            println!("Annotations could be verified to have no contradictions")
        } else {
            println!("Contradiction to annotations found.")
        }
    }

    /// Propagates proof goals top down (i.e. from output predicate head to rule bodies)
    pub fn goal_propagation(&mut self, verifier: &mut RuleVerifier, fuel: i32) {
        let output_predicates = self.program.output_predicates();

        let mut changed: HashSet<Tag> = HashSet::new();
        // start with output predicates and turn them into goals
        for predicate in output_predicates {
            let output_annotations = self.program.predicate_to_global_annotation(predicate);
            for annotation in output_annotations {
                verifier.add_output_verification_goal(annotation);
            }
            changed.insert(predicate.clone());
        }
        for i in 0..fuel {
            let mut new_goals: HashSet<Tag> = HashSet::new();
            if changed.is_empty() {
                break;
            }
            for predicate in changed {
                for index in self.program.rules_with_head_predicate(&predicate) {
                    let rule = &self.program.rules()[index];
                    new_goals = verifier.backward_prop_goals(&predicate, rule);
                }
            }
            changed = new_goals;
            let goals = verifier.verification_goals();
            println!("iteration {i} - goals:");
            for (predicate, goal) in goals {
                println!("{predicate}: {goal}");
            }
        }
    }

    /// not every derivation step, or otherwise give an inductive or spec predicate
    /// Do this only if we actually have assertions for output predicate (e.g. for each predicate)
    pub fn verify_with_goal_propagation(&mut self) {
        let mut verifier = RuleVerifier::new();

        self.goal_propagation(&mut verifier, 10);

        for fact in self.program.facts() {
            verifier.verify_facts(fact, self.program());
        }

        let mut rule_graph = RuleAnalysisGraph::<GraphConstructorPositive>::new(
            self.program.rules().iter().collect(),
        );

        // Do a topological bottom up propagation & verification
        while let Some(scc) = rule_graph.next_scc() {
            let mut delta = true;
            while delta {
                delta = false;

                for rule_index in &scc {
                    let rule = &self.program.rules()[*rule_index];
                    println!("Checking rule {rule_index}: {rule}");
                    delta = verifier.verify_with_propagation(self.program(), &rule) || delta;
                }
            }
        }
        let mut valid = true;
        for predicate in self.program.output_predicates() {
            valid = verifier.check_goal_state(predicate) && valid;
        }
        if valid {
            println!("Annotations could be verified to have no contradictions")
        } else {
            println!("Contradiction to annotations found, maybe increase fuel")
        }
    }

    /// Verifies and propagates forward any known annotations
    pub fn verify_with_forward_propagation(&mut self) {
        let mut verifier = RuleVerifier::new();
        for fact in self.program.facts() {
            verifier.verify_facts(fact, self.program());
        }

        let mut rule_graph = RuleAnalysisGraph::<GraphConstructorPositive>::new(
            self.program.rules().iter().collect(),
        );

        let rules: Vec<&NormalizedRule> = self.program.rules().iter().collect();
        let graph = PropagationGraph::build_graph(&rules);
        graph.print_graph();
        // Do a topological bottom up propagation & verification
        while let Some(scc) = rule_graph.next_scc() {
            if scc.len() == 1 {
                let rule = &self.program.rules()[scc[0]];
                if !rule.is_recursive() {
                    verifier.verify_with_restrictions(self.program(), &rule);
                    verifier.forward_propagation(self.program(), &rule);
                }
            } else {
            }
            let mut delta = true;
            while delta {
                //TODO: put back delta maybe
                delta = false;

                for rule_index in &scc {
                    let rule = &self.program.rules()[*rule_index];
                    println!("Checking rule {rule_index}: {rule}");
                    //TODO: do check whether recursive, don't do scc, but topological rule sort
                    verifier.verify_with_restrictions(self.program(), &rule);
                }
            }
        }
    }
}
