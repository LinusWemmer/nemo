//! This module defines [Termination_Annotation].

use std::{collections::HashSet, fmt::Display, hash::Hash};

use crate::rule_model::{
    error::{ValidationReport, validation_error::ValidationError},
    origin::Origin,
    pipeline::id::ProgramComponentId,
};

use super::{
    ComponentBehavior, ComponentIdentity, ComponentSource, IterableComponent, IterablePrimitives,
    IterableVariables, ProgramComponentKind,
    atom::Atom,
    component_iterator, component_iterator_mut,
    term::{
        Term,
        primitive::{Primitive, variable::Variable},
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub enum TerminationDirection {
    Increasing,
    Decreasing,
}

#[derive(Debug, Clone)]
pub struct TerminationAnnotation {
    /// Origin of this component
    origin: Origin,
    /// Id of this component
    id: ProgramComponentId,
    /// predicate of the annotation
    predicate: Atom,
    /// direction of the termination
    direction: TerminationDirection,
    /// body of the annotation
    body: Term,
}

impl TerminationAnnotation {
    /// Create a new [TerminationAnnotation].
    pub fn new(predicate: Atom, body: Term, direction: TerminationDirection) -> Self {
        Self {
            origin: Origin::Created,
            id: ProgramComponentId::default(),
            predicate,
            direction,
            body,
        }
    }

    /// Return a reference to the predicate that is annotated
    pub fn predicate(&self) -> &Atom {
        &self.predicate
    }

    /// Return the body of the operations
    pub fn body(&self) -> &Term {
        &self.body
    }

    /// Return the termination direction
    pub fn direction(&self) -> &TerminationDirection {
        &self.direction
    }

    /// Return a mutable reference to the operations as mut
    pub fn body_mut(&mut self) -> &mut Term {
        &mut self.body
    }

    /// Return the set of variables in the predicate of the annotation
    pub fn predicate_variables(&self) -> HashSet<&Variable> {
        self.predicate.variables().collect::<HashSet<_>>()
    }

    /// Return the set of variables that are bound in the operations
    pub fn restricted_variables(&self) -> HashSet<&Variable> {
        self.body.variables().collect::<HashSet<_>>()
    }
}

impl ComponentBehavior for TerminationAnnotation {
    fn kind(&self) -> ProgramComponentKind {
        ProgramComponentKind::TerminationAnnotation
    }

    /// Validate the termination annotation, the following should hold:
    ///     * All variables in the body occur in the atom
    fn validate(&self) -> Result<(), ValidationReport> {
        let mut report = ValidationReport::default();

        for child in self.children() {
            report.merge(child.validate());
        }

        // Check if every restricted variable occurs in the "predicate" of the restriction
        let atom_vars = self.predicate_variables();
        for var in self.restricted_variables() {
            if !atom_vars.contains(var) {
                report.add(self, ValidationError::ConflictingAnnotationVariables);
                return report.result();
            }
        }

        // Check if all body are equality or unequality TODO: check for geq, gt, leq, lt
        // TODO: check if body atom contains numeric terms ?

        report.result()
    }

    fn boxed_clone(&self) -> Box<dyn super::ProgramComponent> {
        Box::new(self.clone())
    }
}

impl ComponentSource for TerminationAnnotation {
    type Source = Origin;

    fn origin(&self) -> Origin {
        self.origin.clone()
    }

    fn set_origin(&mut self, origin: Origin) {
        self.origin = origin;
    }
}

impl ComponentIdentity for TerminationAnnotation {
    fn id(&self) -> ProgramComponentId {
        self.id
    }

    fn set_id(&mut self, id: ProgramComponentId) {
        self.id = id;
    }
}

impl IterableComponent for TerminationAnnotation {
    fn children<'a>(&'a self) -> Box<dyn Iterator<Item = &'a dyn super::ProgramComponent> + 'a> {
        let predicate_iterator = component_iterator(std::iter::once(&self.predicate));
        let body_iterator = component_iterator(std::iter::once(&self.body));

        Box::new(predicate_iterator.chain(body_iterator))
    }

    fn children_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut dyn super::ProgramComponent> + 'a> {
        let predicate_iterator = component_iterator_mut(std::iter::once(&mut self.predicate));
        let body_iterator = component_iterator_mut(std::iter::once(&mut self.body));

        Box::new(predicate_iterator.chain(body_iterator))
    }
}

impl Display for TerminationAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#assert ")?;
        let pred = &self.predicate.to_string();
        write!(f, "{pred}")?;
        f.write_str(": ")?;

        write!(f, "{}", self.body)?;

        f.write_str(" .")
    }
}

impl PartialEq for TerminationAnnotation {
    fn eq(&self, other: &Self) -> bool {
        self.predicate == other.predicate && self.body == other.body
    }
}

impl Eq for TerminationAnnotation {}

impl Hash for TerminationAnnotation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.predicate.hash(state);
        self.body.hash(state);
    }
}

impl IterableVariables for TerminationAnnotation {
    fn variables<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Variable> + 'a> {
        Box::new(
            self.predicate()
                .iter()
                .flat_map(|atom| atom.variables())
                .chain(self.body().variables()),
        )
    }

    fn variables_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Variable> + 'a> {
        let predicate_variables = self.predicate.variables_mut();

        let restriction_variables = self.body.variables_mut();

        Box::new(predicate_variables.chain(restriction_variables))
    }
}

impl IterablePrimitives for TerminationAnnotation {
    fn primitive_terms<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Primitive> + 'a> {
        let predicate_primitives = self.predicate.primitive_terms();
        let restriction_primitives = self.body().primitive_terms();

        Box::new(predicate_primitives.chain(restriction_primitives))
    }

    fn primitive_terms_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Term> + 'a> {
        let predicate_primitives = self.predicate.primitive_terms_mut();
        let restriction_primitives = self.body.primitive_terms_mut();

        Box::new(predicate_primitives.chain(restriction_primitives))
    }
}
