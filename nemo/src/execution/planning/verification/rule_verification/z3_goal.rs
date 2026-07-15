//! This module defines verification goals for output predicates

use std::{collections::HashMap, fmt::Display};

use nemo_physical::datavalues::DataValue;
use z3::{
    Goal, Tactic,
    ast::{Ast, Bool, Int},
};

use crate::{
    execution::planning::{
        normalization::{
            atom::{body::BodyAtom, head::HeadAtom},
            global_annotation::NormalizedGlobalAnnotation,
        },
        verification::rule_verification::z3_translation::RuleTranslator,
    },
    rule_model::components::term::primitive::{
        Primitive::{self, Ground},
        variable::Variable,
    },
};

/// Represents the status of the VerificationGoal,
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum VerificationStatus {
    /// Goal has been proven at least once
    /// Importantly, it can still be disproven
    Proven,
    /// Goal has been disproven, so guaranteed doesn't hold.
    Refuted,
    /// Truth of goal unknown
    Unknown,
}

/// Represents a goal necessary to prove output predicates
#[derive(Debug, Clone)]
pub struct VerificationGoal {
    /// Variable names in restriction
    pos_vars: Vec<Int>,
    /// Theory for bounds on the head TODO: change to single formula that gets changed &simplified
    verification_goals: Vec<Bool>,
    /// The current status of proving the goal
    status: VerificationStatus,
}

impl VerificationGoal {
    /// creates a new VerificationGoal from the annotation for the output predicates
    pub fn new_from_annotation(annotation: &NormalizedGlobalAnnotation) -> Self {
        let pos_vars: Vec<Int> = (0..annotation.head().arity())
            .map(|n| Int::fresh_const(&format!("V{n}")))
            .collect();

        let var_cache: HashMap<Variable, Int> = annotation
            .variables()
            .enumerate()
            .map(|(pos, v)| (v.clone(), pos_vars[pos].clone()))
            .collect();

        let translator = RuleTranslator::new();
        let goals: Vec<Bool> = annotation
            .body()
            .iter()
            .map(|op| {
                translator
                    .translate_operation(op, &var_cache)
                    .as_bool()
                    .expect("Translation should work")
            })
            .collect();

        Self {
            pos_vars,
            verification_goals: goals,
            status: VerificationStatus::Unknown,
        }
    }

    /// Creates a goal from unfolding a rule body
    pub fn new_from_propagation(
        atom: &BodyAtom,
        var_cache: &HashMap<Variable, Int>,
        prop_goal: &Bool,
    ) -> Self {
        let pos_vars: Vec<Int> = (0..atom.arity())
            .map(|n| Int::fresh_const(&format!("V{n}")))
            .collect();
        let substitution: Vec<(&Int, &Int)> = atom
            .terms()
            .zip(pos_vars.iter())
            .map(|(v_rule, v_pos)| {
                (
                    var_cache.get(v_rule).expect("var should be registered"),
                    v_pos,
                )
            })
            .collect();

        let tactic_simplify = Tactic::new("ctx-solver-simplify");
        let goal = Goal::new(false, false, false);

        let verification_goal = prop_goal.substitute(&substitution);
        goal.assert(&verification_goal);

        let result: Vec<Goal> = tactic_simplify
            .apply(&goal, None)
            .expect("simplify tactic failed")
            .list_subgoals()
            .collect();
        let verification_goals = result
            .first()
            .expect("simplification should at least yield true or false")
            .get_formulas();

        Self {
            pos_vars,
            verification_goals,
            status: VerificationStatus::Unknown,
        }
    }
}

impl VerificationGoal {
    /// Sets the status to verified if it hasn't been refuted
    /// returns true if the status changed
    pub fn goal_proven(&mut self) -> bool {
        if self.status == VerificationStatus::Unknown {
            self.status = VerificationStatus::Proven;
            return true;
        }
        false
    }

    /// Returns true if the current status of the goal is proven
    pub fn is_proven(&self) -> bool {
        self.status == VerificationStatus::Proven
    }

    /// Sets the status to refuted, returns true if something changed
    pub fn goal_refuted(&mut self) -> bool {
        if self.status == VerificationStatus::Refuted {
            return false;
        }
        self.status = VerificationStatus::Refuted;
        true
    }

    /// Returns true if the goal has been refuted
    pub fn is_refuted(&self) -> bool {
        self.status == VerificationStatus::Refuted
    }
}

impl VerificationGoal {
    /// Adds a goal to the appropriate predicate
    pub fn add_propagated_goal(
        &mut self,
        atom: &BodyAtom,
        var_cache: &HashMap<Variable, Int>,
        prop_goal: &Bool,
    ) {
        let substitution: Vec<(&Int, &Int)> = atom
            .terms()
            .zip(self.pos_vars.iter())
            .map(|(v_rule, v_pos)| {
                (
                    var_cache.get(v_rule).expect("var should be registered"),
                    v_pos,
                )
            })
            .collect();

        let tactic_simplify = Tactic::new("ctx-solver-simplify");
        let goal = Goal::new(false, false, false);

        let new_goal = prop_goal.substitute(&substitution);

        goal.assert(&new_goal);
        goal.assert(&Bool::and(&self.verification_goals));

        let result: Vec<Goal> = tactic_simplify
            .apply(&goal, None)
            .expect("simplify tactic failed")
            .list_subgoals()
            .collect();

        if let Some(goal) = result.first() {
            let new_goal = goal.get_formulas();
            self.verification_goals = new_goal;
        }
        // TODO: do emptiness check
        //self.verification_goals.push(new_goal);
    }

    /// Returns proof goal statements for the head atom
    pub fn goal_from_head_atom(
        &self,
        head_atom: &HeadAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Vec<Bool> {
        let substitution: Vec<(Int, Int)> = self
            .pos_vars
            .iter()
            .zip(head_atom.terms())
            .map(|(v_goal, p_body)| match p_body {
                Primitive::Variable(variable) => (
                    v_goal.clone(),
                    var_cache
                        .get(variable)
                        .expect("var should be registered")
                        .clone(),
                ),
                Ground(ground_term) => (
                    v_goal.clone(),
                    Int::from_i64(ground_term.value().to_i64_unchecked()),
                ),
            })
            .collect();
        let sub_ref: Vec<(&Int, &Int)> = substitution.iter().map(|(s, n)| (s, n)).collect();

        self.verification_goals
            .iter()
            .map(|g| g.substitute(&sub_ref))
            .collect()
    }

    /// Returns proof goal statements for the head atom
    pub fn goal_from_body_atom(
        &self,
        body_atom: &BodyAtom,
        var_cache: &HashMap<Variable, Int>,
    ) -> Vec<Bool> {
        let substitution: Vec<(Int, Int)> = self
            .pos_vars
            .iter()
            .zip(body_atom.terms())
            .map(|(v_goal, v_body)| {
                (
                    v_goal.clone(),
                    var_cache
                        .get(v_body)
                        .expect("var should be registered")
                        .clone(),
                )
            })
            .collect();
        let sub_ref: Vec<(&Int, &Int)> = substitution.iter().map(|(s, n)| (s, n)).collect();

        self.verification_goals
            .iter()
            .map(|g| g.substitute(&sub_ref))
            .collect()
    }
}

impl Display for VerificationGoal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for goal in &self.verification_goals {
            write!(f, "{}", goal)?;
        }
        Ok(())
    }
}
