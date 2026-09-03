//! This Module Defines define [AnnotationAnalyzer]

use crate::execution::{
    planning::{
        normalization::{
            global_annotation::NormalizedGlobalAnnotation, program::NormalizedProgram,
        },
        verification::{
            annotation_analysis::rule_selection::RuleAnalysisGraph, edb_analysis::EdbAnalyzer,
            rule_verification::RuleVerifier, termination_verification::TerminationVerifier,
        },
    },
    selection_strategy::dependency_graph::graph_positive::GraphConstructorPositive,
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
    pub fn verify_annotations(&mut self, ct: bool) {
        let mut verifier = RuleVerifier::new();

        let mut valid = true;
        for fact in self.program.facts() {
            valid = verifier.verify_facts(fact, self.program()) && valid;
        }

        self.rule_graph.reset_scc_count();

        for (rule_index, rule) in self.program.rules().iter().enumerate() {
            println!("Checking rule {rule_index}:");
            if self
                .program
                .predicate_has_global_annotation(&rule.head()[0].predicate())
            {
                valid = verifier.verify_rule(self.program(), rule) && valid;
            } else {
                println!("\t Rule {rule_index} head predicate not annotated.");
            }
        }

        if valid {
            println!("Value annotations could be verified to have no contradictions");
            if ct {
                self.check_termination(&verifier);
            }
        } else {
            println!("Correctness of annotations could not be verified.");
            if ct {
                println!(
                    "As value annotations could not be verified, termination check is aborted."
                )
            }
        }
    }

    /// Verifies and propagates forward any known annotations
    pub fn verify_with_forward_propagation(&mut self, ct: bool) {
        let mut verifier = RuleVerifier::new();

        let mut valid = true;
        for fact in self.program.facts() {
            valid = verifier.verify_facts(fact, self.program()) && valid;
        }

        self.rule_graph.reset_scc_count();

        verifier.gather_filters(&self.program);

        // Do a topological bottom up propagation & verification
        while let Some(scc) = self.rule_graph.next_scc() {
            let mut delta = true;
            while delta {
                delta = false;
                for rule_index in &scc {
                    let rule = &self.program.rules()[*rule_index];
                    delta = verifier.forward_propagation(self.program(), rule) || delta;
                }
            }
        }

        for (rule_index, rule) in self.program.rules().iter().enumerate() {
            println!("Checking rule {rule_index}:");
            if self
                .program
                .predicate_has_global_annotation(&rule.head()[0].predicate())
            {
                valid = verifier.verify_with_restrictions(self.program(), rule) && valid;
            } else {
                println!("\t Rule {rule_index} head predicate not annotated.");
            }
        }
        if valid {
            println!("Value annotations could be verified to have no contradictions");
            if ct {
                self.check_termination(&verifier);
            }
        } else {
            println!("Correctness of annotations could not be verified.");
            if ct {
                println!(
                    "As value annotations could not be verified, termination check is aborted."
                )
            }
        }
    }

    /// Checks whether termination of the program can be verified
    pub fn check_termination(&mut self, rule_verifier: &RuleVerifier) {
        let edb_analyser = EdbAnalyzer::new(self.program(), self.rule_graph.clone());
        let mut valid = true;
        let restrictions = rule_verifier.predicate_restriction();
        let verifier =
            TerminationVerifier::new(edb_analyser, restrictions.clone(), self.program.clone());
        self.rule_graph.reset_scc_count();
        println!("Checking termination...");
        while let Some(scc) = self.rule_graph.next_scc() {
            if scc.len() == 1 {
                if !self.program.rules()[scc[0]].is_recursive() {
                    continue;
                }
            }
            println!("Checking scc: {:?}", scc);

            valid = verifier.check_scc_termination(&scc) && valid;
        }
        if valid {
            println!("Termination for all components could be verified.");
        } else {
            println!("Failed to prove termination.");
        }
    }
}
