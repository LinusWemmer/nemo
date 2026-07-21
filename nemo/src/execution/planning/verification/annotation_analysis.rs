//! This Module Defines define [AnnotationAnalyzer]

use std::collections::HashSet;

use graph_cycles::Cycles;
use petgraph::Graph;

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
                edb_analysis::{self, EdbAnalyzer},
                rule_verification::RuleVerifier,
            },
        },
        selection_strategy::dependency_graph::{
            graph_constructor::DependencyGraphConstructor, graph_positive::GraphConstructorPositive,
        },
    },
    rule_model::components::tag::Tag,
};

//pub mod analysis_report;
pub mod propagation_graph;
pub mod rule_selection;

/// Analyzes the given annotations
#[derive(Debug, Clone)]
pub struct AnnotationAnalyzer {
    /// The program to be analyzed
    program: NormalizedProgram,

    /// The rule graph of the program
    rule_graph: RuleAnalysisGraph<GraphConstructorPositive>,
}

impl AnnotationAnalyzer {
    /// Create a new [AnnotationAnalyzer]
    pub fn new(program: &NormalizedProgram) -> Self {
        let program = program.clone();
        let rule_graph =
            RuleAnalysisGraph::<GraphConstructorPositive>::new(program.rules().iter().collect());
        Self {
            program,
            rule_graph,
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

        self.rule_graph.reset_scc_count();

        let mut valid = true;

        // actually not really necessary
        while let Some(scc) = self.rule_graph.next_scc() {
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

        self.rule_graph.reset_scc_count();

        // Do a topological bottom up propagation & verification
        while let Some(scc) = self.rule_graph.next_scc() {
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

        self.rule_graph.reset_scc_count();

        // Do a topological bottom up propagation & verification
        while let Some(scc) = self.rule_graph.next_scc() {
            if scc.len() == 1 {
                let rule = &self.program.rules()[scc[0]];
                if !rule.is_recursive() {
                    verifier.forward_propagation(self.program(), rule);
                    verifier.verify_with_restrictions(self.program(), rule);
                    continue;
                }
            }

            let prop_graph = PropagationGraph::build_graph(&scc, self.program.rules());
            prop_graph.print_graph();
            println!("weakly acyclic: {}", prop_graph.is_weakly_acyclic());

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

    /// Checks whether termination of the program can be verified
    /// Move to own module
    pub fn check_termination(&mut self) -> bool {
        let edb_analyser = EdbAnalyzer::new(self.program(), self.rule_graph.clone());
        self.rule_graph.reset_scc_count();
        while let Some(scc) = self.rule_graph.next_scc() {
            let propagation_graph = PropagationGraph::build_graph(&scc, self.program.rules());
            if propagation_graph.is_weakly_acyclic() {
                // scc acyclic
            } else {
            }
        }

        true
    }

    /// checks whether the subgraph has critical cycles
    /// Move to own module
    pub fn check_critical_cycles(&self, scc: Vec<usize>, propagation_graph: &PropagationGraph) {
        let special_cycles = propagation_graph.special_cycles();
        for cycle in special_cycles {
            // get all other cycles starting with the same predicate with same rule word attached
            // Check if at least one is bound (lower or upper or in general, depending on annotation)
        }
    }
}
