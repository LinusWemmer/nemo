//! This module defines [RelationTypes]

use std::collections::HashSet;

use nemo_physical::datavalues::ValueDomain;

#[derive(Debug, Clone)]
pub struct RelationTypes {
    /// arity of the predicate
    arity: usize,

    /// sorts of the position
    sorts: Vec<HashSet<ValueDomain>>,
    //TODO: differentiate between empty, ie no type, and any type
}

impl RelationTypes {
    ///Creates a new [RelationTypes] object
    pub fn new(arity: usize) -> Self {
        Self {
            arity,
            sorts: vec![HashSet::default(); arity],
        }
    }
}

impl RelationTypes {
    /// Get the Type for the given position, panics if outside of arity
    pub fn types_at_position(&self, pos: usize) -> &HashSet<ValueDomain> {
        if (pos + 1) >= self.arity {
            panic!("tried to get type from position larger than arity");
        }
        &self.sorts[pos]
    }

    /// Returns true if the given type is valid for position pos
    pub fn contains_type_at_position(&self, pos: usize, sort: &ValueDomain) -> bool {
        self.sorts[pos].contains(sort)
    }
}
