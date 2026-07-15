//! This module defines [NormalizedTypeAnnotation]

use std::fmt::Display;

use nemo_physical::datavalues::ValueDomain;

use crate::rule_model::components::tag::Tag;

/// Represents a normalized Globaltype Annotation
#[derive(Debug, Clone)]
pub struct NormalizedTypeAnnotation {
    ///Predicate which is type annotated
    predicate: Tag,

    /// arity of the predicate
    arity: usize,

    /// Type Annotations for Head
    sorts: Vec<ValueDomain>,
}

impl NormalizedTypeAnnotation {
    /// Return the head of the annotation
    pub fn predicate(&self) -> Tag {
        self.predicate.clone()
    }

    /// Returns the arity of the annotation
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// Return the list of sorts operations of the annotation
    pub fn sorts(&self) -> &Vec<ValueDomain> {
        &self.sorts
    }
}

impl NormalizedTypeAnnotation {
    /// Normalizes the global annotation
    pub fn normalize_type_annotation(
        annotation: &crate::rule_model::components::type_annotation::TypeAnnotation,
    ) -> Self {
        let predicate = annotation.predicate().clone();
        let sorts: Vec<ValueDomain> = annotation.sorts().iter().cloned().collect();
        let arity = sorts.len();
        Self {
            predicate,
            arity,
            sorts,
        }
    }
}

impl Display for NormalizedTypeAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#type ")?;
        let pred = &self.predicate.to_string();
        write!(f, "{pred}")?;
        f.write_str(": ")?;

        for (index, op) in self.sorts.iter().enumerate() {
            write!(f, "{:#?}", op)?;

            if index < self.sorts.len() - 1 {
                f.write_str(", ")?;
            }
        }
        Ok(())
    }
}
