//! This Module Defines define [AnnotationAnalyzer]

use std::{collections::{HashMap, HashSet}, ops::Range};

use crate::{
    execution::{
        planning::{
            normalization::{
                global_annotation::NormalizedGlobalAnnotation, 
                program::NormalizedProgram, 
                rule::NormalizedRule,
            }, verification::{annotation_analysis::rule_selection::RuleAnalysisGraph, restriction::{RANGE_INF, RangeRestriction}, smt_builder::Lowering}
        },
        selection_strategy::dependency_graph::{
            graph_constructor::{DependencyGraph, DependencyGraphConstructor},
            graph_positive::GraphConstructorPositive
        }
    }, rule_model::components::{
        tag::Tag, term::primitive::{Primitive, variable::Variable}
    }
};

pub mod rule_selection;
pub mod analysis_report;

/// Analyzes the given annotations
#[derive(Debug, Default, Clone)]
pub struct AnnotationAnalyzer{
    /// The program to be analized
    program: NormalizedProgram,

    /// The Set of Restrictions on the predicate with respective arity
    unary_restrictions: HashMap<(Tag,usize), RangeRestriction>

}

impl AnnotationAnalyzer{

    /// Create a new [AnnotationAnalyzer]
    pub fn new(program: &NormalizedProgram) -> Self{
        let program = program.clone();
        Self {
            program,
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
        variable_restrictions: &mut HashMap<Variable, Range<i64>>
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
                println!("Annotation {} for {} cannot be verified", restriction_from_annotation, predicate.0)
            } else {
                print!("{}: ", predicate.0.name());
                println!("{propagated_restriction} satisfies annotation {restriction_from_annotation}");
            }
        }
        true
    }


    /// Forward propagation of the annotations through the program, returns true if this works
    // TODO: change return type
    pub fn propagate_annotations(&mut self){

        // TODO: change the report to be of different type later
        let mut _analysis_report = String::new();

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
                if restriction.verify_ground_atom(fact).is_err(){
                    // TODO: move to report, give annotation that isn't matched
                    println!("The fact {} doesn't satisfy the annotations.", fact);
                }
                print!("Ranges of {}: ", fact.predicate());
                println!("{}", restriction);
            } 
        }

        let mut rule_graph = RuleAnalysisGraph::<GraphConstructorPositive>::new(self.program.rules().iter().collect());

        // TODO: maybe change restriction from range to sets of >/<
        // Do a topological bottom up propagation
        while let Some(scc) = rule_graph.next_scc(){
            let mut delta = true;
            while delta{
                delta = false;
                // for scc
                for rule_index in &scc{
                    let rule = &self.program.rules()[*rule_index];
                    println!("{}", rule);
                    // propagate & collect non arithmetic predicates through scc

                    let mut variable_restrictions: HashMap<Variable, Range<i64>> = HashMap::<Variable, Range<i64>>::default();
                    // TODO: move this into rule_var restrictions and return, this doesn't need to be mut otherwise
                    //Restrictions on the variables in the rule at current iteration
                    self.rule_var_restrictions(rule, &mut variable_restrictions);

                    let sat = Lowering::check_rule(rule, &variable_restrictions).expect("smt call didn't work");
                        /* idea:
                        * Generate The formulas from the rule annotation
                        * First: check whether the annotations are actually met
                        * Check whether these match with the variable restrictions
                        * If yes: propagate the extra restrictions (intersection based)
                        * If no: Assume the rule cannot fire and skip propagating to the head
                         */
                    // Make actual head pred restrictions from variable restrictions,TODO: maybe infer restriction for ground terms?
                    if sat{
                        // TODO: just to test, change to actually collecting all
                        let annotation_ops: Vec<crate::execution::planning::normalization::operation::Operation> = rule.annotations().iter()
                            .flat_map(|ann| ann.body())
                            .map(|op| op.clone())
                            .collect();

                        let rule_vars: Vec<&Variable> = rule.variables().collect();

                        let op_vars: HashSet<Variable> = rule.operations().iter()
                            .flat_map(|op|op.variables())
                            .cloned()
                            .collect();
                        let head_vars: HashSet<Variable> = rule.head().iter()
                            .flat_map(|head| head.variables())
                            .cloned()
                            .collect();
                        let arith_head_vars: HashSet<Variable> = op_vars.intersection(&head_vars)
                            .cloned()
                            .collect();

                        
                        // TODO: this needs to be changed to not cause non-termination in case of recursive predicate
                        // TODO: maybe intersect and map with var res
                        // the rest can be optimized much cheaper than with smt call
                        let arith_head_var_ranges = Lowering::get_head_var_range(
                            &variable_restrictions, 
                            &annotation_ops,
                            rule.operations(), 
                            &arith_head_vars, 
                            rule_vars
                        ).expect("Getting max/min range failed");

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
                            
                            for (pos, var) in var_pos_in_head{
                                match (variable_restrictions.get(var), arith_head_var_ranges.get(var)){
                                    (None, None) => (),
                                    (None, Some(range)) =>
                                        delta = head_range_res.range_union(pos, range) || delta,
                                    (Some(range), None) => 
                                        delta = head_range_res.range_union(pos, range) || delta,
                                    (Some(range_1), Some(range_2)) => {
                                        let inter_range = RangeRestriction::intersect_range(range_1, range_2);
                                        delta = head_range_res.range_union(pos, &inter_range) || delta;
                                    },
                                }
                                // TODO: maybe check if it matches the assert here already?
                            }
                            //println!("{}", head_range_res);
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