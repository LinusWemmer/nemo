//! This module defines verification goals for output predicates

use std::{collections::HashMap, fmt::Display};

use nemo_physical::datavalues::DataValue;
use z3::{
    Goal, Solver, Tactic,
    ast::{Ast, Bool, Int},
};

use crate::{
    execution::planning::{
        normalization::{
            atom::{
                body::BodyAtom,
                head::{self, HeadAtom},
            },
            global_annotation::NormalizedGlobalAnnotation,
            input_annotation::NormalizedInputAnnotation,
        },
        verification::rule_verification::z3_translation::RuleTranslator,
    },
    rule_model::components::term::primitive::{
        Primitive::{self, Ground},
        variable::Variable,
    },
};

/// Represents the status of the VerificationGoal
#[derive(Debug, Clone, Copy)]
pub enum VerificationStatus {
    Proven,
    Refuted,
    Unknown,
}

/// Represents a goal necessary to prove output predicates
#[derive(Debug, Clone)]
pub struct VerificationGoal {
    /// Variable names in restriction
    pos_vars: Vec<Int>,
    /// Theory for bounds on the head TODO: change to single formula that gets changed &simplified
    /// TODO: maybe vec<Bool>?
    goals: Bool,
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

        let goal = Bool::and(&body);

        Self {
            pos_vars,
            goals: goal,
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

        let goals = prop_goal.substitute(&substitution);
        Self {
            pos_vars,
            goals,
            status: VerificationStatus::Unknown,
        }
    }
}

impl VerificationGoal {
    /// Sets the status to verified
    pub fn goal_proven(&mut self) {
        self.status = VerificationStatus::Proven
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
        let new_goal = prop_goal.substitute(&substitution);
        // TODO: simplify or do emptiness check
        self.goals = Bool::and(&[&self.goals, &new_goal])
    }

    /// Returns proof goal statements for the head atom
    pub fn goal_from_head(&self, head_atom: &HeadAtom, var_cache: &HashMap<Variable, Int>) -> Bool {
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
        self.goals.substitute(&sub_ref)
    }
}
