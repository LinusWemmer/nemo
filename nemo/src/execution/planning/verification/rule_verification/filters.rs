//! This module defines filter_predicates on predicates represented as z3 formulas

use std::collections::HashMap;

use z3::ast::{Bool, Int};

use crate::{
    execution::planning::{
        normalization::operation::Operation,
        verification::rule_verification::z3_translation::RuleTranslator,
    },
    rule_model::components::term::primitive::{
        Primitive::{self},
        variable::Variable,
    },
};

/// Represents a simple filter expression
#[derive(Debug, Clone)]
pub struct Filter {
    filter_operation: Operation,
}

impl Filter {
    /// Creates a new filter
    pub fn new(filter_operation: Operation) -> Self {
        Self { filter_operation }
    }

    /// Applies the filter to the given term
    pub fn get_filter(&self, term: &Primitive, var_cache: &HashMap<Variable, Int>) -> Bool {
        let translator = RuleTranslator::new();
        let op_var = self
            .filter_operation
            .variables()
            .next()
            .expect("filter expression should contain a variable");
        let smt_term = translator.translate_primitive(term, var_cache);

        let var_cache_new: HashMap<Variable, Int> =
            HashMap::from([(op_var.clone(), smt_term.clone())]);
        translator
            .translate_operation(&self.filter_operation, &var_cache_new)
            .as_bool()
            .expect("filter should return boolean expression")
    }
}
