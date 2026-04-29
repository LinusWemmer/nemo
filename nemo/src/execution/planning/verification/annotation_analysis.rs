//! This Module Defines define [AnnotationAnalyzer]

use std::{collections::{HashMap, HashSet}, ops::Range};

use crate::{
    execution::{
        planning::{
            normalization::{
                global_annotation::NormalizedGlobalAnnotation, 
                program::NormalizedProgram, 
                rule::NormalizedRule, 
                rule_annotation
            },
            verification::{restriction::{RANGE_INF, RangeRestriction}, smt_builder::Lowering}
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

    /// Dependency Graph of the underlying program (TODO: use this to optimize the propagation loop)
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

}


impl AnnotationAnalyzer{

    /// Gets the annotations for all edb predicates in the program
    pub fn edb_annotations(program: &NormalizedProgram) -> impl Iterator<Item = &NormalizedGlobalAnnotation> {
        let derived = program.derived_predicates();

        program.global_annotations()
        .iter()
        .filter(|annotation|
            !derived.contains(&NormalizedGlobalAnnotation::head(annotation).predicate()))
    }

    /// Gets the restrictions on the frontier variables based on previous restrictions in the body
    pub fn rule_var_restrictions(
        &self,
        rule: &NormalizedRule,
        variable_restrictions: &mut HashMap<Variable, Range<i32>>
    ){
        let rule_vars = rule.variables().collect::<HashSet<_>>();
        for atom in rule.positive(){
            let predicate = (atom.predicate(), atom.arity());

            if let Some(body_restriction) = self.unary_restrictions.get(&predicate){

                // All predicate positions in the body atom that contain a frontier var
                let frontier_pos = atom.terms()
                .enumerate()
                .filter(|(_, var)| rule_vars.contains(var));

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


    /// Verifies whether the global annotation holds given the current restrictions
    pub fn verify_global_annotation(&self, annotation :&NormalizedGlobalAnnotation) -> bool{
        let predicate= (annotation.head().predicate(), annotation.head().arity());

        if let Some(propagated_restriction) = self.unary_restrictions.get(&predicate){
            
            if !propagated_restriction.verify_no_empty_term(){
                panic!("There is an empty term for some annotation for {}", predicate.0)
            }
            
            let restriction_from_annotation = RangeRestriction::from_global_annotation(annotation);
            
            if !restriction_from_annotation.verify_compatibility(propagated_restriction){
                println!("annotation for {} cannot be verified", predicate.0)
            }

            print!("Ranges of {}: ", predicate.0.name());
            println!("{}", propagated_restriction);
        }
        true
    }


    /// Forward propagation of the annotations through the program, returns true if this works
    // TODO: change return type
    pub fn propagate_annotations(&mut self){

        // Construct unary restrictions for the edb annotations
        let derived = self.program.derived_predicates();

        let mut base_predicates : HashSet<(Tag, usize)> = self.program.predicates()
            .filter(|(pred, _)| !derived.contains(pred)).collect();

        for fact in self.program.facts(){
            base_predicates.insert((fact.predicate(), fact.arity()));
        }

        for (predicate, arity) in base_predicates{
            let annotations = self.program.predicate_to_global_annotation(&predicate);  

            for annotation in annotations{
                let new_restriction = RangeRestriction::from_global_annotation(annotation);

                self.unary_restrictions
                    .entry((predicate.clone(), arity))
                    .and_modify(|old_restriction| old_restriction.range_intersection(&new_restriction))
                    .or_insert(new_restriction);
            }
        }

        // Verify all facts 
        for fact in self.program.facts(){
            if let Some(restriction) = self.unary_restrictions.get(&(fact.predicate(), fact.arity())){
                if !restriction.verify_ground_atom(fact){
                    println!("The fact {} doesn't satisfy its restrictions.", fact)
                }
                print!("Ranges of {}: ", fact.predicate());
                println!("{}", restriction);
            } 
        }

        // Iterate over the loops while something changes
        // TODO: probably move this to its own method
        // support using horn rules or smth for e.g ?Y = ?X +1
        // TODO: don't propagate if the some range is already empty
        let mut delta = true;
        while delta{
            delta = false;

            for rule in self.program.rules(){
                
                let mut variable_restrictions: HashMap<Variable, Range<i32>> = HashMap::<Variable, Range<i32>>::default();
                // TODO: move this into rule_var restrictions and return, this doesn't need to be mut otherwise
                //Restrictions on the variables in the rule at current iteration
                self.rule_var_restrictions(rule, &mut variable_restrictions);

                let sat = Lowering::check_rule(rule, &variable_restrictions).expect("smt call didn't work");
                    /* idea:
                    * Generate The formulas from the rule annotation
                    * Check whether these match with the variable restrictions
                    * If yes: propagate the extra restrictions (intersection based)
                    * If no: Assume the rule cannot fire and skip propagating to the head
                     */
                // TODO: just to test, change to actually collecting all
                let annotation_ops = rule.annotations().iter()
                    .flat_map(|ann| ann.body())
                    .map(|op| op.clone())
                    .collect();

                let vars: Vec<&Variable> = rule.variables().collect();
                
                let head_vars: HashSet<Variable> = rule.head().iter()
                    .flat_map(|head| head.variables())
                    .map(|var| var.clone())
                    .collect();

                // TODO: restrict only to vars that occur in arithmetic predicates,
                // the rest can be optimized much cheaper than with smt call
                let foo = Lowering::get_frontier_range(&variable_restrictions, &annotation_ops, rule.operations(), &head_vars, vars);

                // Make actual head pred restrictions from variable restrictions,TODO: maybe add restriction for ground terms?
                if sat{
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

                        // Update the ranges TODO: should this maybe be completely moved into range_union?
                        for (pos, var) in var_pos_in_head{
                            if let Some(new_range) = variable_restrictions.get(var){
                                delta = head_range_res.range_union(pos, new_range) || delta;
                            } 
                            // TODO: maybe check if it matches the assert here already?
                        }
                    }
                }
                
            }
        }

        // Verify every global annotation for derived predicates
        for annotation in self.program.global_annotations(){
            if self.program.derived_predicates().contains(&annotation.head().predicate()){
                self.verify_global_annotation(annotation);
            }            
        }

    }
}