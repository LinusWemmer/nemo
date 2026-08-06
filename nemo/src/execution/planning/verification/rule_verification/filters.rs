//! This module defines filter_predicates on predicates represented as z3 formulas

use std::collections::HashMap;

use z3::ast::{Ast, Bool, Int};

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
#[derive(Debug, Clone, Hash)]
pub struct Filter {
    filter_operation: Bool,
    smt_var: Int,
}

impl Filter {
    /// Creates a new filter
    pub fn new(operation: &Operation) -> Self {
        let translator = RuleTranslator::new();
        let op_var = operation
            .variables()
            .next()
            .expect("filter expression should contain a variable");
        let smt_var = Int::fresh_const("v");
        let var_cache: HashMap<Variable, Int> = HashMap::from([(op_var.clone(), smt_var.clone())]);
        let filter_operation = translator
            .translate_operation(operation, &var_cache)
            .as_bool()
            .expect("filter should return boolean expression");

        Self {
            filter_operation,
            smt_var,
        }
    }

    /// Applies the filter to the given term
    pub fn get_filter(&self, term: &Primitive, var_cache: &HashMap<Variable, Int>) -> Bool {
        let translator = RuleTranslator::new();
        let smt_term = translator.translate_primitive(term, var_cache);
        let substitution: Vec<(&Int, &Int)> = vec![(&self.smt_var, &smt_term)];
        self.filter_operation.substitute(&substitution)
    }
}
