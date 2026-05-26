//! This module defines restrictions on predicates represented as z3 formulas

use std::{collections::HashMap, fmt::Display};

use z3::{
    Goal, Tactic,
    ast::{Ast, Bool, Int},
};

use crate::{
    execution::planning::normalization::atom::head::HeadAtom,
    rule_model::components::term::primitive::{
        Primitive::{self, Ground},
        variable::Variable,
    },
};

/// Represents a restriction using z3 predicates very WIP
#[derive(Debug, Clone)]
pub struct Restriction {
    /// Variable names in restriction
    head_vars: Vec<Int>,
    /// Theory for bounds on the head TODO: change to single formula that gets changed &simplified
    restrictions: Bool,
}

impl Restriction {
    /// Creates a new set of restricitons from GlobalAnnotation (actually not needed, as annotations are directly translated)
    /*pub fn new_from_annotation(annotation: &NormalizedGlobalAnnotation) -> Self {
        let var_cache: HashMap<Variable, Int> = annotation
            .variables()
            .map(|v| {
                (
                    v.clone(),
                    Int::fresh_const(v.name().expect("Anon vars not supported yet")),
                )
            })
            .collect();

        let translator = RuleTranslator::new();
        let body: Vec<Bool> = annotation
            .body()
            .iter()
            .map(|op| {
                translator
                    .translate_operation(op, &var_cache)
                    .as_bool()
                    .expect("Translation should work")
            })
            .collect();

        let res = Bool::and(&body);

        Self {
            var_cache,
            restrictions: vec![res],
        }
    }*/

    /// Creates a new [Restriction] from a propagated formula
    pub fn new_from_propagation(
        head: &HeadAtom,
        var_cache: &HashMap<Variable, Int>,
        prop_restriction: &Bool,
    ) -> Self {
        let head_vars: Vec<Int> = (0..head.arity())
            .map(|n| Int::fresh_const(&format!("V{n}")))
            .collect();

        //TODO: get variables (Int)
        let substitution: Vec<(&Int, &Int)> = head
            .terms()
            .zip(head_vars.iter())
            .filter_map(|(p, n)| match p {
                Primitive::Variable(v) => Some((var_cache.get(v).expect("msg"), n)),
                Ground(_) => None,
            })
            .collect();

        let restrictions = prop_restriction.substitute(&substitution);
        Self {
            head_vars,
            restrictions,
        }
    }

    /// Adds a restriction to the set of restrictions, returns true if something changes, false otherwise
    pub fn add_restriction_from_propagation(
        &mut self,
        head: &HeadAtom,
        var_cache: &HashMap<Variable, Int>,
        prop_restriction: &Bool,
    ) -> bool {
        let substitution: Vec<(&Int, &Int)> = head
            .terms()
            .zip(self.head_vars.iter())
            .filter_map(|(p, n)| match p {
                Primitive::Variable(v) => Some((var_cache.get(v).expect("msg"), n)),
                Ground(_) => None,
            })
            .collect();

        let tactic_simplify = Tactic::new("simplify");
        let goal = Goal::new(false, false, false);

        let new_restrictions = prop_restriction.substitute(&substitution);
        goal.assert(&Bool::or(&[&self.restrictions, &new_restrictions]));

        let result = tactic_simplify
            .apply(&goal, None)
            .expect("simplify tactic failed")
            .list_subgoals()
            .collect::<Vec<Goal>>();

        if let Some(goal) = result.first() {
            self.restrictions = Bool::and(&goal.get_formulas());
        }

        true
    }
}

impl Display for Restriction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.restrictions)
    }
}
