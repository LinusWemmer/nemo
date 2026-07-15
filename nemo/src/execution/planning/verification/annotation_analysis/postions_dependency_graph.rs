use std::collections::{HashMap, HashSet};

use crate::{
    execution::planning::normalization::rule::NormalizedRule,
    rule_model::components::{tag::Tag, term::primitive::variable::Variable},
};

pub struct PositionDependencyGraph {
    graph: petgraph::graph::DiGraph<(Tag, usize), ()>,
    rule_to_node_index: Vec<petgraph::graph::NodeIndex>, //(TODO:predicate to node index)
}

impl PositionDependencyGraph {
    /// Builds a dependency graph for the strongly connected components of the rule
    /// The nodes are positions in the predicate and the edges are dependencies between positions
    pub fn build_graph(rules: &[&NormalizedRule]) -> Self {
        let rule_count = rules.len();

        let mut predicate_to_rules_body = HashMap::<Tag, Vec<usize>>::new();
        let mut predicate_to_rules_head = HashMap::<Tag, Vec<usize>>::new();

        for (rule_index, rule) in rules.iter().enumerate() {
            for (body_predicate, _) in rule.predicates_positive() {
                let indices = predicate_to_rules_body.entry(body_predicate).or_default();

                indices.push(rule_index);
            }

            for (head_predicate, _) in rule.predicates_head() {
                let indices = predicate_to_rules_head.entry(head_predicate).or_default();

                indices.push(rule_index);
            }
        }

        let mut graph = petgraph::graph::DiGraph::new();
        let predicates: HashSet<(Tag, usize)> = rules.iter().flat_map(|r| r.predicates()).collect();
        let mut predicate_pos_to_node_index = HashMap::default();

        for (tag, arity) in predicates {
            for pos in 0..arity {
                let node_index = graph.add_node((tag, pos));
                predicate_pos_to_node_index.insert((tag, pos), node_index);
            }
        }

        for rule in rules {
            let head = rule.head()[0];
            let head_vars_at_pos: Vec<(usize, &Variable)> = head
                .terms()
                .enumerate()
                .filter_map(|(pos, t)| match t {
                    crate::rule_model::components::term::primitive::Primitive::Variable(
                        variable,
                    ) => Some((pos, variable)),
                    _ => None,
                })
                .collect();

            let vars_together_in_operations: Vec<HashSet<Variable>> = rule
                .operations()
                .iter()
                .map(|op| op.variables().cloned().collect::<HashSet<Variable>>())
                .collect();

            for body_atom in rule.positive() {
                let tag = body_atom.predicate();
                for (pos, var) in body_atom.terms().enumerate() {}
            }
        }
        for (head_predicate, head_rules) in predicate_to_rules_head {
            if let Some(body_rules) = predicate_to_rules_body.get(&head_predicate) {
                for head_index in head_rules {
                    for &body_index in body_rules {
                        let node_head = rule_to_node_index[head_index];
                        let node_body = rule_to_node_index[body_index];

                        graph.add_edge(node_head, node_body, ());
                    }
                }
            }
        }

        Self {
            graph,
            rule_to_node_index,
        }
    }
}
