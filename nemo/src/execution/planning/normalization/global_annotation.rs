//! This module defines [NormalizedGlobalAnnotation]

use crate::execution::planning::normalization::{
  atom::head::HeadAtom, 
  generator::VariableGenerator,
  operation::Operation};



/// Represents a normalized Global Annotation
#[derive(Debug, Clone)]
pub struct NormalizedGlobalAnnotation{
    ///Headatom of the annotation TODO: maybe make this a body atom?
    head: HeadAtom,

    /// Restrictions placed on the 
    body: Vec<Operation>,
}

impl NormalizedGlobalAnnotation{

    /// Return the head of the annotation
    pub fn head (&self) -> &HeadAtom{
        &self.head
    }

    /// Return the list of body operations of the annotation
    pub fn body (&self) -> &Vec<Operation>{
        &self.body
    }
}

impl NormalizedGlobalAnnotation{

    /// Normalizes the global annotation
    pub fn normalize_global_annotaion(annotation: &crate::rule_model::components::global_annotation::GlobalAnnotation)
    -> Self
    {
        let mut generator = VariableGenerator::default();
        let atom = annotation.predicate();
        let (head, new_operations, new_aggregation) =
        HeadAtom::normalize_atom(&mut generator, atom);

        if !new_operations.is_empty() || new_aggregation.is_some() {
            panic!("Operations and aggregations in annotation head aren't supported");
        }
        let body = annotation.body()
            .iter()
            .map(Operation::normalize_body_operation)
            .collect::<Vec<_>>();

        Self {
            head,
            body,
        }
  }
}
