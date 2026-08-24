//! Defines [EdbAnalyzer]

use std::{collections::HashSet, fmt::Display};

use crate::{
    execution::{
        planning::{
            normalization::{
                operation::Operation, program::NormalizedProgram, rule::NormalizedRule,
            },
            verification::annotation_analysis::rule_selection::RuleAnalysisGraph,
        },
        selection_strategy::dependency_graph::graph_positive::GraphConstructorPositive,
    },
    rule_model::components::{
        tag::Tag,
        term::{
            operation::operation_kind::OperationKind,
            primitive::{Primitive, variable::Variable},
        },
    },
};

/// Tool to check which predicate positions contain only edb values
#[derive(Debug, Clone)]
pub struct EdbAnalyzer {
    edb_positions: HashSet<(Tag, usize)>,
}

impl EdbAnalyzer {
    /// Propagate the ebd positions through the rule
    /// returns true if something changed
    pub fn propagate_positions(
        edb_positions: &mut HashSet<(Tag, usize)>,
        rejected_positions: &mut HashSet<(Tag, usize)>,
        rule: &NormalizedRule,
    ) -> bool {
        let mut delta = false;
        let head = &rule.head()[0];
        let rejected_positions_clone = rejected_positions.clone();
        for (head_pos, prim) in head
            .terms()
            .enumerate()
            .filter(|(pos_h, _)| !rejected_positions_clone.contains(&(head.predicate(), *pos_h)))
        {
            match prim {
                Primitive::Variable(var_h) => {
                    // Var occurs in body position of edb_position
                    if rule.positive().iter().any(|b| {
                        b.terms().enumerate().any(|(body_pos, var_b)| {
                            (var_b == var_h) && edb_positions.contains(&(b.predicate(), body_pos))
                        })
                    }) {
                        delta = edb_positions.insert((head.predicate(), head_pos)) || delta;
                    }
                    // Var occurs in body position of rejected_position
                    else if rule.positive().iter().any(|b| {
                        b.terms().enumerate().any(|(body_pos, var_b)| {
                            (var_b == var_h)
                                && rejected_positions.contains(&(b.predicate(), body_pos))
                        })
                    }) {
                        delta = rejected_positions.insert((head.predicate(), head_pos)) || delta;
                        edb_positions.remove(&(head.predicate(), head_pos));
                    }
                    // Variable occurs in critical operation
                    else if rule.operations().iter().any(|op| {
                        op.variables()
                            .any(|v_op| (v_op == var_h) && EdbAnalyzer::critical_operation(&op))
                    }) {
                        delta = rejected_positions.insert((head.predicate(), head_pos)) || delta;
                        edb_positions.remove(&(head.predicate(), head_pos));
                    }
                }

                Primitive::Ground(_) => {
                    edb_positions.insert((head.predicate(), head_pos));
                }
            }
        }
        delta
    }

    /// Creates a new [EdbAnalyzer]
    pub fn new(
        program: &NormalizedProgram,
        mut rule_graph: RuleAnalysisGraph<GraphConstructorPositive>,
    ) -> Self {
        rule_graph.reset_scc_count();
        let mut edb_positions: HashSet<(Tag, usize)> = HashSet::new();
        let mut rejected_positions: HashSet<(Tag, usize)> = HashSet::new();
        let derived_predicates = program.derived_predicates();

        let edb_predicates = program.predicates().filter_map(|(tag, arity)| {
            if derived_predicates.contains(&tag) {
                None
            } else {
                Some((tag, arity))
            }
        });

        for (tag, arity) in edb_predicates {
            for i in 0..arity {
                edb_positions.insert((tag.clone(), i));
            }
        }

        let mut delta = true;

        while let Some(scc) = rule_graph.next_scc() {
            while delta {
                delta = false;
                for rule_index in &scc {
                    let rule = &program.rules()[*rule_index];

                    delta = EdbAnalyzer::propagate_positions(
                        &mut edb_positions,
                        &mut rejected_positions,
                        rule,
                    );
                }
            }
            delta = true;
        }
        Self { edb_positions }
    }

    /// Returns true if the operation potentially creates a new value for the variable
    pub fn critical_operation(op: &Operation) -> bool {
        // only var assignments can be critical
        if let Operation::Opreation { kind, subterms } = op
            && matches!(kind, OperationKind::Equal)
        {
            let left = subterms.first().expect("invalid program component");
            let right = subterms.get(1).expect("invalid program component");
            if let Operation::Primitive(_) = left
                && let Operation::Primitive(_) = right
            {
                return false;
            } else {
                return true;
            }
        } else {
            false
        }
    }

    /// Returns all variables that contain values directly from the edb in them
    pub fn edb_vars_in_rule(&self, rule: &NormalizedRule) -> HashSet<Variable> {
        rule.positive()
            .iter()
            .flat_map(|b| {
                b.terms().enumerate().filter_map(|(body_pos, body_var)| {
                    if self.edb_positions.contains(&(b.predicate(), body_pos)) {
                        Some(body_var)
                    } else {
                        None
                    }
                })
            })
            .cloned()
            .collect()
    }
}

impl Display for EdbAnalyzer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("edb positions: ")?;
        for (predicate, pos) in &self.edb_positions {
            write!(f, "({predicate}, {pos}), ")?;
        }
        Ok(())
    }
}
