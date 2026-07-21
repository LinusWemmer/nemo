//! Defines [EdbAnalyzer]

use std::collections::HashSet;

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
            operation::operation_kind::OperationKind, primitive::Primitive,
            primitive::variable::Variable,
        },
    },
};

#[derive(Debug, Clone)]
pub struct EdbAnalyzer {
    edb_positions: HashSet<(Tag, usize)>,
}

impl EdbAnalyzer {
    pub fn new(
        program: &NormalizedProgram,
        mut rule_graph: RuleAnalysisGraph<GraphConstructorPositive>,
    ) -> Self {
        rule_graph.reset_scc_count();
        let mut edb_positions: HashSet<(Tag, usize)> = HashSet::new();
        let mut rejected_positions: HashSet<(Tag, usize)> = HashSet::new();
        let derived_predicates = program.derived_predicates();

        let edb_predicates = program.predicates().filter_map(|(tag, pos)| {
            if derived_predicates.contains(&tag) {
                None
            } else {
                Some((tag, pos))
            }
        });

        edb_positions.extend(edb_predicates);
        let mut delta;

        while let Some(scc) = rule_graph.next_scc() {
            delta = false;
            while delta {
                for rule_index in &scc {
                    let rule = &program.rules()[*rule_index];
                    let head = &rule.head()[0];
                    let rejected_positions_clone = rejected_positions.clone();
                    for (head_pos, prim) in head.terms().enumerate().filter(|(pos_h, _)| {
                        !rejected_positions_clone.contains(&(head.predicate(), *pos_h))
                    }) {
                        match prim {
                            Primitive::Variable(var_h) => {
                                if rule.positive().iter().any(|b| {
                                    b.terms().enumerate().any(|(body_pos, var_b)| {
                                        (var_b == var_h)
                                            && edb_positions.contains(&(b.predicate(), body_pos))
                                    })
                                }) {
                                    delta =
                                        edb_positions.insert((head.predicate(), head_pos)) || delta;
                                } else {
                                    if rule.operations().iter().any(|op| {
                                        if op.variables().any(|v_op| v_op == var_h) {
                                            return EdbAnalyzer::critical_operation(&op);
                                        }
                                        false
                                    }) {
                                        delta = rejected_positions
                                            .insert((head.predicate(), head_pos))
                                            || delta;
                                    }
                                }
                            }
                            Primitive::Ground(_) => {
                                edb_positions.insert((head.predicate(), head_pos));
                            }
                        }
                    }
                }
            }
        }

        Self { edb_positions }
    }

    /// Checks whether the given positions is bound with respect to a scc
    /// Bound if:
    /// *edb-position
    /// *A operation where all other variables contained are edb-annotations or bound
    /// *TODO: lower stratum
    /// *Bound by some annotation
    pub fn is_bound(
        &self,
        variable: &Variable,
        rule: &NormalizedRule,
        program: &NormalizedProgram,
    ) -> bool {
        //rule.positive().iter().flat_map(|b| b.is)
        todo!()
    }

    /// Returns true if the operation creates a new value for the variable
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
            }
            true
        } else {
            false
        }
    }
}
