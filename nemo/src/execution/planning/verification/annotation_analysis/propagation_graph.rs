//! This module defines [PropagationGraph]
use std::collections::{HashMap, HashSet};

use graph_cycles::Cycles;
use itertools::Itertools;

use crate::{
    execution::planning::normalization::rule::NormalizedRule,
    rule_model::components::{tag::Tag, term::primitive::Primitive::Variable},
};

use petgraph::{Directed, Graph, dot::Dot, prelude::NodeIndex};

/// Propagation Graph a la callauti
#[derive(Debug, Clone)]
pub struct PropagationGraph {
    /// Labelled graph of predicate positions. False if var in head&body, True if part of function
    graph: petgraph::graph::DiGraph<(Tag, usize), (usize, bool)>,
    predicate_pos_to_node_index: HashMap<(Tag, usize), NodeIndex>, //(TODO:predicate to node index)
}

impl PropagationGraph {
    /// print the graph
    pub fn print_graph(&self) {
        println!("{:?}", Dot::new(&self.graph));
    }

    /// Returns the petgraph graph
    pub fn graph(&self) -> &Graph<(Tag, usize), (usize, bool), Directed> {
        &self.graph
    }

    /// Returns all special cycles
    pub fn special_cycles(&self) -> Vec<Vec<NodeIndex>> {
        let mut special_cycles = Vec::new();
        for cycle in self.graph.cycles() {
            let size = cycle.len();
            if cycle.iter().enumerate().any(|(c_i, current_node)| {
                let c_j = c_i + 1 % size;
                let next_node: NodeIndex = cycle[c_j];
                if let Some(edge_index) = self.graph.find_edge(*current_node, next_node) {
                    self.graph.edge_weight(edge_index).expect("msg").1
                } else {
                    false
                }
            }) {
                special_cycles.push(cycle);
            }
        }
        special_cycles
    }

    /// Returns true if the graph is weakly acyclic
    pub fn is_weakly_acyclic(&self) -> bool {
        for cycle in self.graph.cycles() {
            let size = cycle.len();
            if cycle.iter().enumerate().any(|(c_i, current_node)| {
                let c_j = c_i + 1 % size;
                let next_node: NodeIndex = cycle[c_j];
                if let Some(edge_index) = self.graph.find_edge(*current_node, next_node) {
                    self.graph.edge_weight(edge_index).expect("msg").1
                } else {
                    false
                }
            }) {
                return false;
            }
        }
        true
    }
}

impl PropagationGraph {
    /// Builds a dependency graph for the strongly connected components of the program
    /// The nodes are positions in the predicate and the edges are dependencies between positions
    /// Only computes for the given scc
    pub fn build_graph(positions: &Vec<usize>, rules: &Vec<NormalizedRule>) -> Self {
        let mut graph = petgraph::graph::DiGraph::new();

        let scc_rules: Vec<(&NormalizedRule, usize)> = positions
            .iter()
            .map(|rule_index| (&rules[*rule_index], rule_index.clone()))
            .collect();

        let predicates: HashSet<(Tag, usize)> =
            scc_rules.iter().flat_map(|(r, _)| r.predicates()).collect();
        let mut predicate_pos_to_node_index = HashMap::default();

        for (tag, arity) in predicates {
            for pos in 0..arity {
                let node_index = graph.add_node((tag.clone(), pos));
                predicate_pos_to_node_index.insert((tag.clone(), pos), node_index);
            }
        }

        for (rule, rule_index) in scc_rules {
            let head_atom = &rule.head()[0];

            for (pos_h, term) in head_atom.terms().enumerate() {
                match term {
                    Variable(var_h) => {
                        for body_atom in rule.positive() {
                            for (pos_b, var_b) in body_atom.terms().enumerate() {
                                if var_b == var_h {
                                    let node_body = predicate_pos_to_node_index
                                        .get(&(body_atom.predicate(), pos_b))
                                        .expect("pos should exist");
                                    let node_head = predicate_pos_to_node_index
                                        .get(&(head_atom.predicate(), pos_h))
                                        .expect("pos should exist");

                                    graph.add_edge(*node_body, *node_head, (rule_index, false));
                                }
                                for op in rule.operations() {
                                    if op.variables().contains(var_h)
                                        && op.variables().contains(var_b)
                                    {
                                        let node_body = predicate_pos_to_node_index
                                            .get(&(body_atom.predicate(), pos_b))
                                            .expect("pos should exist");
                                        let node_head = predicate_pos_to_node_index
                                            .get(&(head_atom.predicate(), pos_h))
                                            .expect("pos should exist");
                                        graph.add_edge(*node_body, *node_head, (rule_index, true));
                                    };
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        Self {
            graph,
            predicate_pos_to_node_index,
        }
    }
}
