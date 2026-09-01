//! This module defines [NormalizedGlobalAnnotation]

use std::fmt::Display;

use crate::{
    execution::planning::normalization::{
        atom::{body::BodyAtom, head::HeadAtom},
        generator::VariableGenerator,
        operation::Operation,
    },
    rule_model::components::term::primitive::{Primitive, variable::Variable},
};

/// Represents a normalized Global Annotation
#[derive(Debug, Clone)]
pub struct NormalizedGlobalAnnotation {
    ///Headatom of the annotation
    head: BodyAtom,

    /// Restrictions placed on the head atom
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

    /// Returns a list of vars for which the restriction provides an upper bound if applied to the body atom
    ///
    /// # Panics
    /// Panics if the predicates of the annotation and atom don't match
    pub fn bound_above_vars(&self, atom: &HeadAtom) -> Vec<Variable> {
        if atom.predicate() != self.head.predicate() {
            panic!("Annotation doesn't match atom")
        }
        let bound_above_vars: Vec<&Variable> = self
            .body()
            .iter()
            .filter_map(|b| b.is_upper_bound())
            .collect();
        self.head()
            .terms()
            .zip(atom.terms())
            .filter(|(v_ann, _)| bound_above_vars.contains(&v_ann))
            .filter_map(|(_, term)| match term {
                Primitive::Variable(v_atom) => Some(v_atom.clone()),
                Primitive::Ground(_) => None,
            })
            .collect()
    }

    /// Returns a list of vars for which the restriction provides a lower bound if applied to the body atom
    ///
    /// # Panics
    /// Panics if the predicates of the annotation and atom don't match
    pub fn bound_below_vars(&self, atom: &HeadAtom) -> Vec<Variable> {
        if atom.predicate() != self.head.predicate() {
            panic!("Annotation doesn't match atom")
        }
        let bound_above_vars: Vec<&Variable> = self
            .body()
            .iter()
            .filter_map(|b| b.is_lower_bound())
            .collect();
        self.head()
            .terms()
            .zip(atom.terms())
            .filter(|(v_ann, _)| bound_above_vars.contains(&v_ann))
            .filter_map(|(_, term)| match term {
                Primitive::Variable(v_atom) => Some(v_atom.clone()),
                Primitive::Ground(_) => None,
            })
            .collect()
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
            panic!(
                "Invalid annotation: operations used in annotation atom, which is not supported"
            );
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
