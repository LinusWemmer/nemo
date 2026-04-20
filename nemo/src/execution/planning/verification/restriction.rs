//! This module defines restrictions coming from assertion annotations

use std::{collections::HashMap, ops::Range};

use nemo_physical::datavalues::DataValue;

use crate::{execution::planning::normalization::{
    atom::ground::GroundAtom, global_annotation::NormalizedGlobalAnnotation, operation::Operation
    },
    rule_model::components::term::primitive::{Primitive::{self, Ground}, variable::Variable}};

use crate::rule_model::components::term::operation::operation_kind::OperationKind;

/// Infinite Range
pub const RANGE_INF: Range<i32> = i32::MIN..i32::MAX;

/// Represents a range restriction for now, very WIP
#[derive(Debug, Clone, Default)]
pub struct RangeRestriction{
    
    /// Maps positions in a predicate to logical formulas/ranges? 
    /// WIP, this should probably be some other datatype, e.g. a vector
    //range_res: HashMap<usize,Range<usize>>,
    range_res: HashMap<usize, Range<i32>>
}

impl RangeRestriction{
    /// Returns the Map of restrictions
    pub fn range_res(&self) -> &HashMap<usize, Range<i32>>{
        &self.range_res
    }

    /// Get the range of a single position within a predicate
    pub fn restriction_at_pos(&self, position: &usize) -> Option<&Range<i32>>{
        self.range_res.get(position)
    }
}

impl RangeRestriction {
    /// Creates a new set of range restrictions without any restrictions
    pub fn new() -> Self{
        Self {
            range_res: HashMap::default() 
        }
    }

    /// Creates a new range restriction from a map of positions two ranges
    pub fn new_from_map(range_map: &HashMap<usize, Range<i32>> ) -> Self{
        Self { 
            range_res: range_map.clone()
        }
    }

    /// Insert the given range at the position
    pub fn insert_range(&mut self, position: usize, range: Range<i32>){
        self.range_res.insert(position, range);
    }

    /// updates the range based on the given operation
    /// TODO: should probably return whether the range actually updated
    /// TODO: differentiate between "conjunctive" and "disjunctive" range updates
    pub fn update_range_from_op(
        ranges: &mut HashMap<Variable, Range<i32>>, 
        variable: &Variable,
        term: &Operation, 
        kind: &OperationKind
    ){

        // For now: only allow one data value on the other side of an (in)equality  
        let data_value: i32 = match term {
            Operation::Primitive(Ground(ground_term)) =>
                ground_term.value().to_i32_unchecked(),
            _ => panic!("There should only be a value on the right side")
        };
        // TODO: This could probably be made more elegant with build in rust functions, like .entry().or_default
        if ranges.contains_key(variable) {
            //TODO: here, some warning / report feature should be added for incompatible ranges or something or reducing ranges
            let restriction = ranges.get(variable).expect("something went wrong");
            match kind{
                OperationKind::NumericGreaterthaneq => {
                    ranges.insert(variable.clone(),data_value..restriction.end);},
                OperationKind::NumericGreaterthan => {
                    ranges.insert(variable.clone(), data_value+1..restriction.end);},
                OperationKind::NumericLessthaneq => {
                    ranges.insert(variable.clone(), restriction.start..data_value+1);},
                OperationKind::NumericLessthan => {
                    ranges.insert(variable.clone(), restriction.start..data_value);},
                _ => panic!("unsupported operation in annotation")
            }

        } else {
            match kind{
                OperationKind::NumericGreaterthaneq => {
                    ranges.insert(variable.clone(),data_value..i32::MAX);},
                OperationKind::NumericGreaterthan => {
                    ranges.insert(variable.clone(), data_value+1..i32::MAX);},
                OperationKind::NumericLessthaneq => {
                    ranges.insert(variable.clone(), i32::MIN..data_value+1);},
                OperationKind::NumericLessthan => {
                    ranges.insert(variable.clone(), i32::MIN..data_value);},
                _ => panic!("unsupported operation in annotation")
            }
        }
    }

    /// Return the intersection of two ranges, might result in an empty intersection
    pub fn intersect_range(range_1: &Range<i32>, range_2: &Range<i32>) -> Range<i32>{
        let start = range_1.start.max(range_2.start);
        let end = range_1.end.min(range_2.end);
        start..end
    }

    /// Combines two ranges inclusively, TODO: only if not empty
    pub fn combine_range(range_1: &Range<i32>, range_2: &Range<i32>) -> Range<i32>{
        let start = range_1.start.min(range_2.start);
        let end = range_1.end.max(range_2.end);
        start..end
    }
    
    /// Takes two range restrictions and calculates the union, returns true if the range was updated
    pub fn range_union(&mut self, position: usize, new_range: &Range<i32>) -> bool{
        let old_range = self.range_res.insert(position, new_range.clone());
        match old_range {
            Some(range) => {
                let combined = RangeRestriction::combine_range(&range, new_range);
                self.range_res.insert(position, combined.clone());
                if range == combined || combined.is_empty(){
                    return false
                } else {
                    return true
                }
            },
            None => true
        }        
    }

    /// Returns true if the Ground atom satisfies the constraint, false otherwise
    pub fn verify_ground_atom(&self, atom: &GroundAtom) -> bool {
        for (position, ground_term) in atom.terms().enumerate(){
            if let Some(range) = self.range_res().get(&position){
                let data_value: i32 = ground_term.value().to_i32_unchecked();
                if !range.contains(&data_value){
                    return false;
                }
            }
        }
        true
    }

    /// Returns true if the restriction isn't empty for some term
    pub fn verify_no_empty_term(&self) -> bool{
        for range in self.range_res.values(){
            if range.is_empty(){
                return false
            }
        }
        true
    }

    /// Creates a new range restriction from a global annotation
    pub fn from_global_annotation(annotation: &NormalizedGlobalAnnotation) -> Self{
        let mut range_res =  HashMap::<usize, Range<i32>>::new();
        //let arity = annotation.head().arity();

        
        let mut ranges = HashMap::<Variable,Range<i32>>::new();
     
        // Generate the ranges for the variables, it should probably be checked whether everything is valid (TODO), i.e. unequals
        for operation in annotation.body(){
            match operation{
                
                Operation::Opreation { kind, subterms } => {
                    let left = subterms.first().expect("invalid program component");
                    let right = subterms.get(1).expect("invalid program component");
                    if let Operation::Primitive(Primitive::Variable(variable)) = left {
                        RangeRestriction::update_range_from_op(&mut ranges, variable, right, kind);
                    } else if let Operation::Primitive(Primitive::Variable(variable)) = right {
                        RangeRestriction::update_range_from_op(&mut ranges, variable, left, kind);
                    }                    
                } ,
                _ => panic!("Global annotations should not contain primitive operations as annotation"),
            }
        }

        //Match the variable ranges to terms in the atom
        for (position, primitive) in annotation.head().terms().enumerate(){
            match primitive{
                Primitive::Variable(variable) => {
                    if let Some(range) = ranges.get(variable){
                        range_res.insert(position, range.clone());
                    }
                },
                Ground(_) => panic!("TODO: ground terms in annotaion head not supported yet"),
            }
        }
        Self { 
            range_res,
        }
    }
}

impl PartialEq for RangeRestriction{
    fn eq(&self, other: &Self) -> bool {
        self.range_res == other.range_res
    }
}

