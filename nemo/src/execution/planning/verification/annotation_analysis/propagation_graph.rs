//! This module defines [PropagationGraph]
use std::collections::{HashMap, HashSet};

use graph_cycles::Cycles;
use itertools::Itertools;

use crate::{
    execution::planning::normalization::{
        operation::Operation, program::NormalizedProgram, rule::NormalizedRule,
    },
    rule_model::components::{
        tag::Tag,
        term::{
            operation::operation_kind::OperationKind,
            primitive::{Primitive, variable::Variable},
        },
    },
};

use petgraph::{Directed, Direction, Graph, dot::Dot, prelude::NodeIndex, visit::EdgeRef};

/// Propagation Graph (like weak acyclicity)
#[derive(Debug, Clone)]
pub struct PropagationGraph {
    /// Labelled graph of predicate positions. False if var in head&body, True if part of function
    graph: petgraph::graph::DiGraph<(Tag, usize), (usize, bool)>,
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

    /// Provides the predicates that are contained in a cycle
    pub fn nodes_to_predicates(&self, cycle: &Vec<NodeIndex>) -> Vec<Tag> {
        cycle
            .iter()
            .map(|n| {
                self.graph
                    .node_weight(*n)
                    .expect("weight missing")
                    .0
                    .clone()
            })
            .collect()
    }

    /// Returns the sequence of rule applications for a given cycle
    /// TODO: handle multi-edges and so on
    /*pub fn edges_from_cycle(&self, cycle: &Vec<NodeIndex>) -> Vec<(usize, bool)> {
        let mut cycle_edges = Vec::new();
        let size = cycle.len();
        for c_i in 0..size {
            let c_j = (c_i + 1) % size;
            let current_node = cycle[c_i];
            let next_node = cycle[c_j];
            if let Some(edge_index) = self.graph.find_edge(current_node, next_node) {
                cycle_edges.push(
                    self.graph
                        .edge_weight(edge_index)
                        .expect("edge should exist")
                        .clone(),
                );
            }
        }
        cycle_edges
    }*/

    /// Gets the set of all nodes that are positions of the same predicate
    pub fn same_predicate(&self, node: NodeIndex) -> HashSet<NodeIndex> {
        let predicate = self
            .graph
            .node_weight(node)
            .expect("there should be a node");
        self.graph
            .node_indices()
            .filter(|n_i| {
                self.graph
                    .node_weight(*n_i)
                    .expect("there should be a weight")
                    .0
                    == predicate.0
            })
            .collect()
    }

    /// Returns the predicate position of the given node
    pub fn node_predicate_pos(&self, node: NodeIndex) -> (Tag, usize) {
        self.graph
            .node_weight(node)
            .expect("there should be a weight")
            .clone()
    }

    /// Returns true if the graph is weakly acyclic
    pub fn is_weakly_acyclic(&self) -> bool {
        for cycle in self.graph.cycles() {
            let size = cycle.len();
            if cycle.iter().enumerate().any(|(c_i, current_node)| {
                let c_j = (c_i + 1) % size;
                let next_node: NodeIndex = cycle[c_j];
                self.graph
                    .edges_connecting(*current_node, next_node)
                    .any(|edge| {
                        self.graph
                            .edge_weight(edge.id())
                            .expect("edge weight should exist")
                            .1
                    })
            }) {
                return false;
            }
        }
        true
    }

    /// Returns the all cycles of the rule propagation graph with special cycles
    pub fn all_rule_cycles(&self) -> Vec<Vec<usize>> {
        let mut cycles = Vec::new();
        let rule_graph = self.rule_graph_from_propagation_graph();
        for cycle in rule_graph.cycles() {
            let rule_cycle = cycle
                .iter()
                .map(|node_index| {
                    *rule_graph
                        .node_weight(*node_index)
                        .expect("There should be a node weight")
                })
                .collect();
            cycles.push(rule_cycle);
        }
        cycles
    }

    /// Builds a rule dependency graph from the propagation graph.
    /// Nodes are rule indices. There is an edge r1 -> r2 if some predicate
    /// position has an incoming edge labeled r1 (r1 writes to it, as a head)
    /// and an outgoing edge labeled r2 (r2 reads from it, as a body atom).
    /// Edge weight is true if either contributing propagation-graph edge was critical.
    pub fn rule_graph_from_propagation_graph(&self) -> Graph<usize, bool, Directed> {
        let mut rule_graph: Graph<usize, bool> = Graph::new();
        let mut rule_to_node: HashMap<usize, NodeIndex> = HashMap::new();

        // Create one rule-graph node per distinct rule index appearing in the propagation graph
        for edge_ref in self.graph.edge_references() {
            let (rule_index, _) = edge_ref.weight();
            rule_to_node
                .entry(*rule_index)
                .or_insert_with(|| rule_graph.add_node(*rule_index));
        }

        // For every position, connect rules that write it (incoming) to rules that read it (outgoing)
        for node in self.graph.node_indices() {
            let incoming: Vec<(usize, bool)> = self
                .graph
                .edges_directed(node, Direction::Incoming)
                .map(|e| *e.weight())
                .collect();
            let outgoing: Vec<(usize, bool)> = self
                .graph
                .edges_directed(node, Direction::Outgoing)
                .map(|e| *e.weight())
                .collect();

            for (r1, critical_in) in &incoming {
                for (r2, _) in &outgoing {
                    let n1 = rule_to_node[r1];
                    let n2 = rule_to_node[r2];
                    let critical = *critical_in;

                    match rule_graph.find_edge(n1, n2) {
                        Some(existing) => {
                            if critical {
                                let w = rule_graph
                                    .edge_weight_mut(existing)
                                    .expect("edge should exist");
                                *w = true;
                            }
                        }
                        None => {
                            rule_graph.add_edge(n1, n2, critical);
                        }
                    }
                }
            }
        }
        println!("{:?}", Dot::new(&rule_graph));
        rule_graph
    }
}

impl PropagationGraph {
    /// Builds a dependency graph for the strongly connected components of the program
    /// The nodes are positions in the predicate and the edges are dependencies between positions
    /// Only computes for the given scc
    pub fn build_graph(program: &NormalizedProgram, rule_indices: &Vec<usize>) -> Self {
        let mut graph = petgraph::graph::DiGraph::new();

        let rules = program.rules();
        let scc_rules: Vec<(&NormalizedRule, usize)> = rule_indices
            .iter()
            .map(|rule_index| (&rules[*rule_index], rule_index.clone()))
            .collect();

        let predicates: HashSet<(Tag, usize)> =
            scc_rules.iter().flat_map(|(r, _)| r.predicates()).collect();
        let mut predicate_pos_to_node_index: HashMap<(Tag, usize), NodeIndex> = HashMap::default();

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
                    Primitive::Variable(var_h) => {
                        let body_vars: HashSet<&Variable> =
                            rule.positive().iter().flat_map(|b| b.terms()).collect();
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
                                //TODO: check if the critical var is actually bound by an edb expression, then it shouldn't be marked
                                //TODO: actually only if not in other body atom

                                for op in rule.operations() {
                                    if PropagationGraph::critical_operation(op) {
                                        if op.variables().contains(var_h)
                                            && op.variables().contains(var_b)
                                            && !body_vars.contains(var_h)
                                            && !PropagationGraph::is_bound(program, rule, var_h)
                                        {
                                            let node_body = predicate_pos_to_node_index
                                                .get(&(body_atom.predicate(), pos_b))
                                                .expect("pos should exist");
                                            let node_head = predicate_pos_to_node_index
                                                .get(&(head_atom.predicate(), pos_h))
                                                .expect("pos should exist");
                                            graph.add_edge(
                                                *node_body,
                                                *node_head,
                                                (rule_index, true),
                                            );
                                        };
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        Self { graph }
    }

    /// Returns true if the variable is bound
    pub fn is_bound(program: &NormalizedProgram, rule: &NormalizedRule, var: &Variable) -> bool {
        let mut lower_bound = false;
        let mut upper_bound = false;
        for op in rule.operations() {
            if !lower_bound
                && let Some(v_bound) = op.is_lower_bound()
                && var == v_bound
            {
                lower_bound = true;
            } else if !upper_bound
                && let Some(v_bound) = op.is_upper_bound()
                && var == v_bound
            {
                upper_bound = true;
            }
        }
        let head_atom = &rule.head()[0];
        let annotations = program.predicate_to_global_annotation(&head_atom.predicate());
        for annotation in annotations {
            if !lower_bound && annotation.bound_below_vars(head_atom).contains(var) {
                lower_bound = true;
            }
            if !upper_bound && annotation.bound_above_vars(head_atom).contains(var) {
                upper_bound = true;
            }
        }

        lower_bound && upper_bound
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
