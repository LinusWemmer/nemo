//! This module defines [NormalizedGlobalAnnotation]

use std::fmt::Display;

use crate::{
    execution::planning::normalization::{
        atom::body::BodyAtom, generator::VariableGenerator, operation::Operation,
    },
    rule_model::components::term::primitive::variable::Variable,
};

/// Represents a normalized Global Annotation
#[derive(Debug, Clone)]
pub struct NormalizedGlobalAnnotation {
    ///Headatom of the annotation
    head: BodyAtom,

    /// Restrictions placed on the head atom, TODO
    body: Vec<Operation>,
}

impl NormalizedGlobalAnnotation {
    /// Return the head of the annotation
    pub fn head(&self) -> &BodyAtom {
        &self.head
    }

    /// Return the list of body operations of the annotation
    pub fn body(&self) -> &Vec<Operation> {
        &self.body
    }
}

impl NormalizedGlobalAnnotation {
    /// Normalizes the global annotation
    pub fn normalize_global_annotation(
        annotation: &crate::rule_model::components::global_annotation::GlobalAnnotation,
    ) -> Self {
        let mut generator = VariableGenerator::default();
        let atom = annotation.predicate();
        let (head, new_operations) = BodyAtom::normalize_atom(&mut generator, atom);

        if !new_operations.is_empty() {
            panic!("Operations and aggregations in annotation head aren't supported");
        }
        let body = annotation
            .body()
            .iter()
            .map(Operation::normalize_body_operation)
            .collect::<Vec<_>>();

        Self { head, body }
    }

    /// Returns all variables of the annotation as an iterator
    pub fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.head().terms()
    }
}

impl Display for NormalizedGlobalAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#assert ")?;
        let pred = &self.head().to_string();
        write!(f, "{pred}")?;
        f.write_str(": ")?;

        for (index, op) in self.body.iter().enumerate() {
            write!(f, "{op}")?;

            if index < self.body.len() - 1 {
                f.write_str(", ")?;
            }
        }
        Ok(())
    }
}
