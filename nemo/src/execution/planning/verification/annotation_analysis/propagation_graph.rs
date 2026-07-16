//! This module defines [PropagationGraph]
use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::{
    execution::planning::normalization::rule::NormalizedRule,
    rule_model::components::{tag::Tag, term::primitive::Primitive::Variable},
};

/// Propagation Graph a la callauti
#[derive(Debug, Clone)]
pub struct PropagationGraph {
    /// Labelled graph of predicate positions. False if var in head&body, True if part of function
    graph: petgraph::graph::DiGraph<(Tag, usize), bool>,
    predicate_pos_to_node_index: HashMap<(Tag, usize), petgraph::prelude::NodeIndex>, //(TODO:predicate to node index)
}

impl PropagationGraph {
    /// print the graph
    pub fn print_graph(&self) {
        println!("{:#?}", self.graph);
    }
}

impl PropagationGraph {
    /// Builds a dependency graph for the strongly connected components of the rule
    /// The nodes are positions in the predicate and the edges are dependencies between positions
    pub fn build_graph(rules: &[&NormalizedRule]) -> Self {
        let mut graph: petgraph::Graph<(Tag, usize), bool> = petgraph::graph::DiGraph::new();

        let predicates: HashSet<(Tag, usize)> = rules.iter().flat_map(|r| r.predicates()).collect();
        let mut predicate_pos_to_node_index = HashMap::default();

        for (tag, arity) in predicates {
            for pos in 0..arity {
                let node_index = graph.add_node((tag.clone(), pos));
                predicate_pos_to_node_index.insert((tag.clone(), pos), node_index);
            }
        }

        for rule in rules {
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

                                    graph.add_edge(*node_body, *node_head, false);
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
                                        graph.add_edge(*node_body, *node_head, true);
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
