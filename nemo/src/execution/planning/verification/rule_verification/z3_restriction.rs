//! This module defines restrictions on predicates represented as z3 formulas

use std::{collections::HashMap, fmt::Display};

use z3::{
    Goal, Optimize, Solver, Tactic,
    ast::{Ast, Bool, Int},
};

use crate::{
    execution::planning::normalization::atom::{body::BodyAtom, head::HeadAtom},
    rule_model::components::term::primitive::{
        Primitive::{self, Ground},
        variable::Variable,
    },
};

/// Represents a restriction using z3 predicates very
/// TODO: restriction are only allowed to be > or similar operations (syntactic check)
#[derive(Debug, Clone)]
pub struct Restriction {
    /// Variable names in restriction
    restriction_head_vars: Vec<Int>,
    /// Theory for bounds on the head
    restrictions: Vec<Bool>,
}

impl Restriction {
    /// Creates a new [Restriction] from a propagated formula
    pub fn new_from_propagation(
        head: &HeadAtom,
        var_cache: &HashMap<Variable, Int>,
        prop_restriction: &Bool,
    ) -> Self {
        let head_vars: Vec<Int> = (0..head.arity())
            .map(|n| Int::fresh_const(&format!("V{n}")))
            .collect();

        let substitution: Vec<(&Int, &Int)> = head
            .terms()
            .zip(head_vars.iter())
            .filter_map(|(p, n)| match p {
                Primitive::Variable(v) => Some((var_cache.get(v).expect("msg"), n)),
                Ground(_) => None,
            })
            .collect();

        let restriction = prop_restriction.substitute(&substitution);
        Self {
            restriction_head_vars: head_vars,
            restrictions: vec![restriction],
        }
    }

    /// Returns the restrictions for a given body atom
    pub fn get_restrictions_for_body(
        &self,
        body_atom: &BodyAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Bool {
        let substitution: Vec<(&Int, &Int)> = self
            .restriction_head_vars
            .iter()
            .zip(body_atom.terms())
            .map(|(v_res, v_body)| {
                (
                    v_res,
                    var_cache.get(v_body).expect("var should be registered"),
                )
            })
            .collect();
        let body_res: Vec<Bool> = self
            .restrictions
            .iter()
            .map(|res| res.substitute(&substitution))
            .collect();

        Bool::or(&body_res)
    }

    /// Checks whether a new restriction actually gives new entailments
    pub fn check_new_entailment(&self, new_restriction: &Bool) -> bool {
        let solver = Solver::new();
        solver.assert(Bool::and(&self.restrictions).not());
        solver.assert(new_restriction);

        match solver.check() {
            z3::SatResult::Unsat => false,
            z3::SatResult::Unknown => false,
            z3::SatResult::Sat => true,
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
            .zip(self.restriction_head_vars.iter())
            .filter_map(|(p, n)| match p {
                Primitive::Variable(v) => Some((var_cache.get(v).expect("msg"), n)),
                Ground(_) => None,
            })
            .collect();
        let tactic_simplify = Tactic::new("ctx-solver-simplify");
        let goal = Goal::new(false, false, false);

        let new_restrictions = prop_restriction.substitute(&substitution);

        if !self.check_new_entailment(&new_restrictions) {
            return false;
        }
        goal.assert(&new_restrictions);

        let result = tactic_simplify
            .apply(&goal, None)
            .expect("simplify tactic failed")
            .list_subgoals()
            .collect::<Vec<Goal>>();

        if let Some(goal) = result.first() {
            self.restrictions.push(Bool::and(&goal.get_formulas()));
            //println!("simplified formulas:{:#?}", goal.get_formulas())
        }
        true
    }

    /// Returns true if the variable position has a lower bound from the given restrictions can be definietly found
    pub fn has_lower_bound(&self, pos: usize) -> bool {
        let pos_var = &self.restriction_head_vars[pos];

        let optimize = Optimize::new();

        optimize.assert(&Bool::or(&self.restrictions));
        optimize.minimize(pos_var);
        optimize.check(&[]); //TODO: might be necesarry to check what kind in order to avoid panic

        match optimize.get_lower(0) {
            Some(a) => !a.to_string().contains("oo"),
            None => false,
        }
    }

    /// Returns true if the variable position has an upper bound from the given restrictions can be definietly found
    pub fn has_upper_bound(&self, pos: usize) -> bool {
        let pos_var = &self.restriction_head_vars[pos];

        let optimize = Optimize::new();

        optimize.assert(&Bool::or(&self.restrictions));
        optimize.maximize(pos_var);
        optimize.check(&[]); //TODO: might be necesarry to check what kind in order to avoid panic

        match optimize.get_upper(0) {
            Some(a) => !a.to_string().contains("oo"),
            None => false,
        }
    }
}

impl Display for Restriction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for restriction in self.restrictions.clone() {
            write!(f, "{}, ", restriction)?;
        }
        Ok(())
    }
}
