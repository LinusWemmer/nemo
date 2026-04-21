//! This Module Defines define [AnnotationAnalyzer]

use std::{collections::HashMap, ops::Range};

use crate::{
    execution::{
        planning::{
            normalization::{
                atom::head::HeadAtom, 
                global_annotation::NormalizedGlobalAnnotation, 
                program::NormalizedProgram, 
                rule::NormalizedRule, 
                rule_annotation
            },
            verification::restriction::{RANGE_INF, RangeRestriction}
        },
        selection_strategy::dependency_graph::{
            graph_constructor::{DependencyGraph, DependencyGraphConstructor},
            graph_positive::GraphConstructorPositive
        }
    }, rule_model::components::{
        tag::Tag, term::primitive::{Primitive, variable::Variable}
    }
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

    /// Gets the restrictions on the frontier variables based on previous restrictions in the body
    pub fn frontier_var_restrictions(
        &self,
        rule: &NormalizedRule,
        variable_restrictions: &mut HashMap<Variable, Range<i32>>
    ){
        let frontier = rule.frontier();
        for atom in rule.positive(){
            let predicate = (atom.predicate(), atom.arity());

            if let Some(body_restriction) = self.unary_restrictions.get(&predicate){

                // All predicate positions in the body atom that contain a frontier var
                let frontier_pos = atom.terms()
                .enumerate()
                .filter(|(_, var)| frontier.contains(var));

                // Intersect the existing restriction on the variables with the body restrictions
                for (pos, var) in frontier_pos{
                    let restrictions_at_pos = body_restriction.range_res()
                        .get(&pos)
                        .unwrap_or(&RANGE_INF);

                    let variable_restriction= variable_restrictions.get(var)
                        .unwrap_or(&RANGE_INF);
                    
                    let updated_restriction = RangeRestriction::intersect_range(restrictions_at_pos, variable_restriction);

                    // Something changed if the range changed meaningfully
                    if updated_restriction != *variable_restriction {
                        variable_restrictions.insert(var.clone(), updated_restriction);
                    } else if updated_restriction.is_empty(){
                        //TODO: temporary measure for testing only, as it may occur only after the nth firing of the rule
                        println!("rule couldn't fire");
                    }
                }

            }
        }
    }

    /// Verifies whether the rule annotation matches the current annotations
    pub fn verify_rule_annotation() -> bool{
        true
    }


    /// Forward propagation of the annotations through the program, returns true if this works
    // TODO: change return type
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
        // TODO: This can also unnecesarily double up the annotations for the same predicate with multiple facts
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

        // Iterate over the loops while something changes
        // TODO: support for rule annotations
        // TODO: probably move this to its own method
        // TODO: don't propagate if the some range is already empty
        let mut delta = true;
        while delta{
            delta = false;

            for rule in self.program.rules(){
                
                // Ranges of the frontier variables
                let mut variable_restrictions: HashMap<Variable, Range<i32>> = HashMap::<Variable, Range<i32>>::default();

                self.frontier_var_restrictions(rule, &mut variable_restrictions);

                // TODO: verify & propagate rule annotations
                /*for rule_annotation in rule.annotations(){
                    /* idea:
                    * Generate The formulas from the rule annotation
                    * Check whether these match with the variable restrictions
                    * If yes: propagate the extra restrictions (intersection based)
                    * If no: Assume the rule cannot fire and skip propagating to the head
                     */
                }*/

                // Make actual head pred restrictions from variable restrictions,TODO: maybe add restriction for ground terms?
                for head_atom in rule.head(){
                    let head_predicate = (head_atom.predicate(), head_atom.arity());

                    let var_pos_in_head = 
                        head_atom.terms().enumerate()
                        .filter_map(|(pos, var)| {
                            match var{
                                Primitive::Variable(variable) => Some((pos,variable)),
                                Primitive::Ground(_) => None,
                            }
                        });
                    
                    // The previous restriction on the head predicate
                    let head_range_res = self.unary_restrictions
                        .entry(head_predicate)
                        .or_insert(RangeRestriction::new());

                    // Update the ranges
                    for (pos, var) in var_pos_in_head{
                        if let Some(new_range) = variable_restrictions.get(var){
                            delta = head_range_res.range_union(pos, new_range) || delta;
                        } 
                    }
                }
            }
        }

        // Verify every global annotation, we should probably again move this to its own function
        // TODO: this should only be done for assert in derived predicates
        // move this to a seperate function called after propagate annotations
        for annotation in self.program.global_annotations(){
            let predicate: (Tag, usize) = (annotation.head().predicate(), annotation.head().arity());

            // TODO: verify even if no restrictions can be found, which should result in an error message
            if let Some(propagated_restriction) = self.unary_restrictions.get(&predicate){
                if !propagated_restriction.verify_no_empty_term(){
                    panic!("There is an empty term for some annotation")
                }
                
                let restriction_from_annotation = RangeRestriction::from_global_annotation(annotation);
                
                if !restriction_from_annotation.verify_compatibility(propagated_restriction){
                    println!("annotation cannot be verified")
                }

                print!("Ranges of {}: ", predicate.0.name());
                println!("{}", propagated_restriction);
            }
        }

    }
}