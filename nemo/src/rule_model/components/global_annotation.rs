//! This module defines [Global_Annotation].

use std::{collections::HashSet, fmt::Display, hash::Hash};

use crate::{rule_model::{
    components::{term::operation::{Operation, operation_kind::OperationKind}},
    error::{ValidationReport, validation_error::ValidationError},
    origin::Origin,
    pipeline::id::ProgramComponentId,
}};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GlobalAnnotationKind {
  Assert,
  Verify,
}

#[derive(Debug, Clone)]
pub struct GlobalAnnotation {
    /// Origin of this component
    origin: Origin,
    /// Id of this component
    id: ProgramComponentId,
    
    /// Kind of Annotation
    kind: GlobalAnnotationKind,
    /// predicate of the annotation
    predicate: Atom,
    /// Restrictions on the variables
    restrictions: Vec<Operation>,

}

impl GlobalAnnotation {
    /// Create a new [GlobalAnnotation].
    pub fn new(kind: GlobalAnnotationKind, predicate: Atom, restrictions: Vec<Operation>) -> Self {
        Self {
            origin: Origin::Created,
            id: ProgramComponentId::default(),
            kind,
            predicate,
            restrictions,
        }
    }

    /// Return a reference to the predicate that is annotated
    pub fn predicate(&self) -> &Atom {
        &self.predicate
    }

    /// Return the kind of the annotation
    pub fn kind(&self) -> GlobalAnnotationKind {
        self.kind
    }

    /// Return the restrictions of the operations
    pub fn restrictions(&self) -> &Vec<Operation> {
        &self.restrictions
    }

    ///TODO Return an iterator over the operations in the body of this annotation TODO: probably ensure these are inequalities?
    /*pub fn restrictions(&self) -> impl Iterator<Item = &Operation> {
        self.restrictions.iter()
    }*/

    /// Return a mutable reference to the operations as mut
    pub fn restrictions_mut(&mut self) -> &mut Vec<Operation> {
        &mut self.restrictions
    }

    /// Return the set of variables in the predicate of the annotation
    pub fn predicate_variables(&self) -> HashSet<&Variable> {
        self.predicate.variables().collect::<HashSet<_>>()
    }

    /// Return the set of variables that are bound in the operations
    pub fn restricted_variables(&self) -> HashSet<&Variable> {
        self.restrictions
            .iter()
            .flat_map(|op| op.variables())
            .collect::<HashSet<_>>()
    }

}

impl ComponentBehavior for GlobalAnnotation {
    fn kind(&self) -> ProgramComponentKind {
        ProgramComponentKind::GlobalAnnotation
    }


    /// Validate the global annotation, the following should hold:
    ///     * All variables in the restrictions occur in the predicate/predicate
    ///     * All restrictions are either eq or unequal at highest level
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
                return report.result()
            }
        }

        // Check if all restrictions are equality or unequality:
        for restriction in self.restrictions(){
            let kind = restriction.operation_kind();
            if !(kind == OperationKind::Equal || kind == OperationKind::Unequals) {
                report.add(self, ValidationError::UnsoppertedAnnotationRestrictions);
                return report.result()
            }
        }

        report.result()
    }

    fn boxed_clone(&self) -> Box<dyn super::ProgramComponent> {
        Box::new(self.clone())
    }
}

impl ComponentSource for GlobalAnnotation {
    type Source = Origin;

    fn origin(&self) -> Origin {
        self.origin.clone()
    }

    fn set_origin(&mut self, origin: Origin) {
        self.origin = origin;
    }
}

impl ComponentIdentity for GlobalAnnotation {
    fn id(&self) -> ProgramComponentId {
        self.id
    }

    fn set_id(&mut self, id: ProgramComponentId) {
        self.id = id;
    }
}

impl IterableComponent for GlobalAnnotation {
    fn children<'a>(&'a self) -> Box<dyn Iterator<Item = &'a dyn super::ProgramComponent> + 'a> {
        let predicate_iterator = component_iterator(std::iter::once(&self.predicate));
        let restrictions_iterator = component_iterator(self.restrictions.iter());

        Box::new(predicate_iterator.chain(restrictions_iterator))
    }

    fn children_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut dyn super::ProgramComponent> + 'a> {
        let predicate_iterator = component_iterator_mut(std::iter::once(&mut self.predicate));
        let restrictions_iterator = component_iterator_mut(self.restrictions.iter_mut());
        
        Box::new(predicate_iterator.chain(restrictions_iterator))
    }

}

impl Display for GlobalAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            GlobalAnnotationKind::Assert => f.write_str("#assert ")?,
            GlobalAnnotationKind::Verify => f.write_str("#verify ")?,
        }

        let pred = &self.predicate.to_string();
        write!(f, "{pred}")?;
        f.write_str(": ")?;

        for (index, op_literal) in self.restrictions.iter().enumerate() {
            write!(f, "{op_literal}")?;

            if index < self.restrictions.len() - 1 {
                f.write_str(", ")?;
            }
        }
        f.write_str(" .")
    }
}

impl PartialEq for GlobalAnnotation {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.predicate == other.predicate && self.restrictions == other.restrictions
    }
}

impl Eq for GlobalAnnotation {}

impl Hash for GlobalAnnotation{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        self.predicate.hash(state);
        self.restrictions.hash(state);
    }
}

impl IterableVariables for GlobalAnnotation {
    fn variables<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Variable> + 'a> {
        Box::new(
            self.predicate()
                .iter()
                .flat_map(|atom| atom.variables())
                .chain(self.restrictions().iter().flat_map(|literal| literal.variables())),
        )
    }

    fn variables_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Variable> + 'a> {
        let predicate_variables = self.predicate.variables_mut();

        let restriction_variables = self
            .restrictions
            .iter_mut()
            .flat_map(|op| op.variables_mut());

        Box::new(predicate_variables.chain(restriction_variables))
    }
}

impl IterablePrimitives for GlobalAnnotation {
    fn primitive_terms<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Primitive> + 'a> {
        let predicate_primitives = self.predicate.primitive_terms();
        let restriction_primitives = self
            .restrictions()
            .iter()
            .flat_map(|literal| literal.primitive_terms());

        Box::new(predicate_primitives.chain(restriction_primitives))
    }

    fn primitive_terms_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Term> + 'a> {
        let predicate_primitives = self.predicate.primitive_terms_mut();
        let restriction_primitives = self
            .restrictions
            .iter_mut()
            .flat_map(|literal| literal.primitive_terms_mut());

        Box::new(predicate_primitives.chain(restriction_primitives))
    }
}
