//! This module defines [NormalizedTerminationAnnotation]

use std::fmt::Display;

use crate::{
    execution::planning::normalization::{
        atom::body::BodyAtom, generator::VariableGenerator, operation::Operation,
    },
    rule_model::components::term::primitive::variable::Variable,
};

/// Represents Direction of Termination
#[derive(Debug, Copy, Clone)]
pub enum TerminationDirection {
    /// Decreasing
    Decreasing,
    /// Increasing
    Increasing,
}

/// Represents a normalized Global Annotation
#[derive(Debug, Clone)]
pub struct NormalizedTerminationAnnotation {
    ///Headatom of the annotation TODO: maybe make this a body atom?
    head: BodyAtom,
    /// Direction in which the termination happesn
    direction: TerminationDirection,
    /// Restrictions placed on the head atom, TODO
    body: Operation,
}

impl NormalizedTerminationAnnotation {
    /// Return the head of the annotation
    pub fn head(&self) -> &BodyAtom {
        &self.head
    }

    /// Return the list of body operations of the annotation
    pub fn body(&self) -> &Operation {
        &self.body
    }

    /// Return the direction
    pub fn direction(&self) -> TerminationDirection {
        self.direction
    }
}

impl NormalizedTerminationAnnotation {
    /// Normalizes the input annotation
    pub fn normalize_termination_annotation(
        annotation: &crate::rule_model::components::termination_annotation::TerminationAnnotation,
    ) -> Self {
        let mut generator = VariableGenerator::default();
        let atom = annotation.predicate();
        let (head, new_operations) = BodyAtom::normalize_atom(&mut generator, atom);

        if !new_operations.is_empty() {
            panic!(
                "Operations and Aggregations should not be used in annotation head, same variables in head not supported yet"
            );
        }
        let body = Operation::normalize_body_operation(annotation.body());

        let direction = match annotation.direction(){
            crate::rule_model::components::termination_annotation::TerminationDirection::Increasing => TerminationDirection::Increasing,
            crate::rule_model::components::termination_annotation::TerminationDirection::Decreasing => TerminationDirection::Decreasing,
        };

        Self {
            head,
            direction,
            body,
        }
    }

    /// Returns all variables of the annotation as an iterator
    pub fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.head().terms()
    }
}

impl Display for NormalizedTerminationAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#assert ")?;
        let pred = &self.head().to_string();
        write!(f, "{pred}")?;
        f.write_str(": ")?;

        write!(f, "{}", self.body)?;

        Ok(())
    }
}
