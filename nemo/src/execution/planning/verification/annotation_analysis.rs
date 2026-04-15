//! This Module Defines define [AnnotationAnalyzer]

use std::collections::HashMap;

use crate::{
    execution::{
        planning::{
            normalization::{
                global_annotation::NormalizedGlobalAnnotation, 
                program::NormalizedProgram, 
                rule::NormalizedRule
            },
            verification::restriction::RangeRestriction
        },
        selection_strategy::dependency_graph::{
            graph_constructor::{DependencyGraph, DependencyGraphConstructor},
            graph_positive::GraphConstructorPositive
        }
    }, rule_model::components::tag::Tag
};

/// Analyzes the given annotations
#[derive(Debug, Default, Clone)]
pub struct AnnotationAnalyzer{
    /// The program to be analized
    program: NormalizedProgram,

    /// Dependency Graph of the underlying program
    /// TODO: change this to a new implementation of predicate graphs (using petgraph)
    dependency_graph: DependencyGraph,
    /// The Set of Restrictions on the predicate with respective arity
    unary_restrictions: HashMap<(Tag,usize), RangeRestriction>

}

impl AnnotationAnalyzer{

    /// Create a new [AnnotationAnalyzer]
    pub fn new(program: &NormalizedProgram) -> Self{
        let dependency_graph = Self::generate_rule_dependency(program);
        let program = program.clone();
        Self {
            program,
            dependency_graph,
            unary_restrictions: HashMap::default(),
        }
    }

    /// Return the underlying program
    pub fn program(&self) -> &NormalizedProgram {
        &self.program
    }

    /// Generates the dependency graph of the given program
    pub fn generate_rule_dependency(program: &NormalizedProgram) -> DependencyGraph{
        let mut rules = Vec::<&NormalizedRule>::default();
        for rule in program.rules(){
            rules.push(rule);
        }
        GraphConstructorPositive::build_graph(&rules)
    }

    //Generates the predicate dependency graph of the positive atoms
    /*pub fn generate_predicate_dependency(program: &NormalizedProgram) -> Graph<(Tag,usize), (), Directed>{
        let mut graph = Graph::<(Tag,usize), (), Directed>::new();
        let mut predicate_to_node_index  = Vec::new();

        for predicate in program.predicates(){
            let node_index = graph.add_node(predicate);
            predicate_to_node_index.push(node_index);
        }


        for rule in program.rules(){
            for head_predicate in rule.predicates_head() {
                for body_predicate in rule.predicates_positive() {
                    graph.add_edge(body_predicate, head_predicate, ());
                }
            }
        }
        graph
    }*/

}


impl AnnotationAnalyzer{

   

    /// Gets the annotations for all edb predicates in the program
    pub fn edb_annotations(program: &NormalizedProgram) -> impl Iterator<Item = &NormalizedGlobalAnnotation> {
        let derived = program.derived_predicates();
        program.global_annotations()
        .iter()
        .filter_map(|annotation| {
            match derived.contains(&NormalizedGlobalAnnotation::head(annotation).predicate()){
                true => None,
                false => Some(annotation)
            }
        })
    }

    /// Propagate the annotations through the program
    pub fn propagate_annotations(&mut self){

        //Construct unary restrictions for the edb annotations -> These won't change anymore
        // This is neccesary because of imports -> i.e. 
        // -> TODO: This would change with imports, if the import predicates are edb
        /*for annotation in AnnotationAnalyzer::edb_annotations(&self.program){
            let restriction = RangeRestriction::from_global_annotation(annotation);
            let predicate = annotation.head().predicate();
            let arity = annotation.head().arity();

            self.unary_restrictions.insert((predicate, arity), restriction);
        }*/

        // Construct annotations for facts, if any -> TODO:This can double up some annotations from the previous step
        // TODO: This can also unnecesarily double upd the annotations for the same predicate with multiple facts
        // -> Verification and generating range need to split up
        for fact in self.program.facts(){
            let annotations = self.program.predicate_to_global_annotation(fact.predicate());
            for annotation in annotations{
                let restriction = RangeRestriction::from_global_annotation(annotation);
                let predicate = annotation.head().predicate();
                let arity = annotation.head().arity();
                    
                //TODO: this shouldn't panic and instead log this somewhere
                if !restriction.verify_ground_atom(fact){
                    panic!("The fact cannot satisfy the annotation")
                }

                self.unary_restrictions.insert((predicate, arity), restriction);
            }
        }
    }
}