//! This module defines [NormalizedGlobalAnnotation]

use std::fmt::Display;

use crate::execution::planning::normalization::{
  atom::head::HeadAtom, 
  generator::VariableGenerator,
  operation::Operation};



/// Represents a normalized Global Annotation
#[derive(Debug, Clone)]
pub struct NormalizedGlobalAnnotation{
    ///Headatom of the annotation TODO: maybe make this a body atom?
    head: HeadAtom,

    /// Restrictions placed on the head atom, TODO
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

impl Display for NormalizedGlobalAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#assert ")?;
        let pred = &self.head().to_string();
        write!(f, "{pred}")?;
        f.write_str(": ")?;

        for (index, op_literal) in self.body.iter().enumerate() {
            write!(f, "{op_literal}")?;

            if index < self.body.len() - 1 {
                f.write_str(", ")?;
            }
        }
        f.write_str(" .")
    }
}