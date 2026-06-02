//! This module defines [Input_Annotation].

use std::{collections::HashSet, fmt::Display, hash::Hash};

use crate::rule_model::{
    components::term::operation::{Operation, operation_kind::OperationKind},
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

#[derive(Debug, Clone)]
pub struct InputAnnotation {
    /// Origin of this component
    origin: Origin,
    /// Id of this component
    id: ProgramComponentId,
    /// predicate of the annotation
    predicate: Atom,
    /// body of the annotation
    body: Vec<Operation>,
}

impl InputAnnotation {
    /// Create a new [InputAnnotation].
    pub fn new(predicate: Atom, body: Vec<Operation>) -> Self {
        Self {
            origin: Origin::Created,
            id: ProgramComponentId::default(),
            predicate,
            body,
        }
    }

    /// Return a reference to the predicate that is annotated
    pub fn predicate(&self) -> &Atom {
        &self.predicate
    }

    /// Return the body of the operations
    pub fn body(&self) -> &Vec<Operation> {
        &self.body
    }

    /// Return a mutable reference to the operations as mut
    pub fn body_mut(&mut self) -> &mut Vec<Operation> {
        &mut self.body
    }

    /// Return the set of variables in the predicate of the annotation
    pub fn predicate_variables(&self) -> HashSet<&Variable> {
        self.predicate.variables().collect::<HashSet<_>>()
    }

    /// Return the set of variables that are bound in the operations
    pub fn restricted_variables(&self) -> HashSet<&Variable> {
        self.body
            .iter()
            .flat_map(|op| op.variables())
            .collect::<HashSet<_>>()
    }
}

impl ComponentBehavior for InputAnnotation {
    fn kind(&self) -> ProgramComponentKind {
        ProgramComponentKind::InputAnnotation
    }

    /// Validate the input annotation, the following should hold:
    ///     * All variables in the body occur in the predicate/predicate
    ///     * All body are either eq or unequal at highest level
    ///     * TODO: validate that assert atoms are only edb/facts, while the ensure need at least one non fact
    ///     => How would I do this?
    /// TODO: change type to allow only infix ops, but all of them
    fn validate(&self) -> Result<(), ValidationReport> {
        let mut report = ValidationReport::default();

        //TODO: validate children
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
        for operation in self.body() {
            let kind = operation.operation_kind();
            if !(kind == OperationKind::Equal || kind == OperationKind::Unequals) {
                report.add(self, ValidationError::UnsoppertedAnnotationRestrictions);
                return report.result();
            }
        }

        report.result()
    }

    fn boxed_clone(&self) -> Box<dyn super::ProgramComponent> {
        Box::new(self.clone())
    }
}

impl ComponentSource for InputAnnotation {
    type Source = Origin;

    fn origin(&self) -> Origin {
        self.origin.clone()
    }

    fn set_origin(&mut self, origin: Origin) {
        self.origin = origin;
    }
}

impl ComponentIdentity for InputAnnotation {
    fn id(&self) -> ProgramComponentId {
        self.id
    }

    fn set_id(&mut self, id: ProgramComponentId) {
        self.id = id;
    }
}

impl IterableComponent for InputAnnotation {
    fn children<'a>(&'a self) -> Box<dyn Iterator<Item = &'a dyn super::ProgramComponent> + 'a> {
        let predicate_iterator = component_iterator(std::iter::once(&self.predicate));
        let body_iterator = component_iterator(self.body.iter());

        Box::new(predicate_iterator.chain(body_iterator))
    }

    fn children_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut dyn super::ProgramComponent> + 'a> {
        let predicate_iterator = component_iterator_mut(std::iter::once(&mut self.predicate));
        let body_iterator = component_iterator_mut(self.body.iter_mut());

        Box::new(predicate_iterator.chain(body_iterator))
    }
}

impl Display for InputAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#assert ")?;
        let pred = &self.predicate.to_string();
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

impl PartialEq for InputAnnotation {
    fn eq(&self, other: &Self) -> bool {
        self.predicate == other.predicate && self.body == other.body
    }
}

impl Eq for InputAnnotation {}

impl Hash for InputAnnotation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.predicate.hash(state);
        self.body.hash(state);
    }
}

impl IterableVariables for InputAnnotation {
    fn variables<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Variable> + 'a> {
        Box::new(
            self.predicate()
                .iter()
                .flat_map(|atom| atom.variables())
                .chain(self.body().iter().flat_map(|literal| literal.variables())),
        )
    }

    fn variables_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Variable> + 'a> {
        let predicate_variables = self.predicate.variables_mut();

        let restriction_variables = self.body.iter_mut().flat_map(|op| op.variables_mut());

        Box::new(predicate_variables.chain(restriction_variables))
    }
}

impl IterablePrimitives for InputAnnotation {
    fn primitive_terms<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Primitive> + 'a> {
        let predicate_primitives = self.predicate.primitive_terms();
        let restriction_primitives = self
            .body()
            .iter()
            .flat_map(|literal| literal.primitive_terms());

        Box::new(predicate_primitives.chain(restriction_primitives))
    }

    fn primitive_terms_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Term> + 'a> {
        let predicate_primitives = self.predicate.primitive_terms_mut();
        let restriction_primitives = self
            .body
            .iter_mut()
            .flat_map(|literal| literal.primitive_terms_mut());

        Box::new(predicate_primitives.chain(restriction_primitives))
    }
}
