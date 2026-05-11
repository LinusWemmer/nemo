//! Selection strategy for rules during statics analysis
use std::marker::PhantomData;

use crate::execution::{
    planning::normalization::rule::NormalizedRule, 
    selection_strategy::dependency_graph::graph_constructor::DependencyGraphConstructor
};



/// Defines Selection for rule propagation
#[derive(Debug)]
pub struct RuleAnalysisGraph<GraphConstructor: DependencyGraphConstructor>{
    _constructor: PhantomData<GraphConstructor>,

    ordered_sccs: Vec<Vec<usize>>,
    current_scc_index: usize,
}

impl<GraphConstructor: DependencyGraphConstructor> RuleAnalysisGraph<GraphConstructor> {

    /// Constructs a new [RuleAnalysisGraph]
    pub fn new(rules: Vec<&NormalizedRule>) -> Self{
        let dependency_graph = GraphConstructor::build_graph(&rules);

        let graph_scc = petgraph::algo::condensation(dependency_graph, true);
        let scc_sorted = petgraph::algo::toposort(&graph_scc, None)
            .expect("The input graph is assured to be acyclic");
        
        let mut ordered_sccs = Vec::new();

        for scc in scc_sorted {
            let scc_rule_indices = graph_scc[scc].clone();
            ordered_sccs.push(scc_rule_indices);
        }

        Self { 
            _constructor: PhantomData,
            ordered_sccs, 
            current_scc_index: 0 }
    }

    /// Returns the next strongly connected component in the dependency graph
    pub fn next_scc(&mut self) -> Option<Vec<usize>>{
        let index = self.current_scc_index;
        self.current_scc_index += 1;
        if self.current_scc_index <= self.ordered_sccs.len(){
            return Some(self.ordered_sccs[index].clone())
        }
        None
    }
}