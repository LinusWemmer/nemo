//! This module defines [NormalizedTypeAnnotation]

use std::fmt::Display;

use crate::{
    execution::planning::normalization::{
        atom::body::BodyAtom, generator::VariableGenerator, operation::Operation,
    },
    rule_model::components::term::primitive::variable::Variable,
};

//TODO: types and so on
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum Sort {
    TypeInt,
    /// Existential variable
    TypeFloat,
    /// Global variable
    TypeString,
    /// Anonymous variable
    TypeAnonymous,
}

/// Represents a normalized Globaltype Annotation
#[derive(Debug, Clone)]
pub struct NormalizedTypeAnnotation {
    ///Predicate which is type annotated
    predicate: Tag,

    /// arity of the predicate
    arity: usize,

    /// Restrictions placed on the head atom, TODO
    body: Vec<Operation>,
}

impl NormalizedTypeAnnotation {
    /// Return the head of the annotation
    pub fn head(&self) -> &BodyAtom {
        &self.head
    }

    /// Return the list of body operations of the annotation
    pub fn body(&self) -> &Vec<Operation> {
        &self.body
    }
}

impl NormalizedTypeAnnotation {
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

impl Display for NormalizedTypeAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#type ")?;
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
