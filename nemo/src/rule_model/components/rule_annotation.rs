//! This module defines [Rule_Annotation].

use std::{collections::HashSet, fmt::Display, hash::Hash};

use crate::{rule_model::{
    components::term::operation::Operation,
    error::ValidationReport,
    origin::Origin,
    pipeline::id::ProgramComponentId,
}};

use super::{
    ComponentBehavior, ComponentIdentity, ComponentSource, IterableComponent,
    IterableVariables, ProgramComponentKind,
    component_iterator, component_iterator_mut,
    term::primitive::variable::Variable,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuleAnnotationKind {
  Requires,
  Ensures,
}

#[derive(Debug, Clone)]
pub struct RuleAnnotation {
    /// Origin of this component
    origin: Origin,
    /// Id of this component
    id: ProgramComponentId,
    /// Kind of Annotation
    kind: RuleAnnotationKind,
    ///WIP: maybe add reference to the rule it refers to
    /// Restrictions on the variables
    restrictions: Vec<Operation>,
}

impl RuleAnnotation {
    /// Create a new [RuleAnnotation].
    pub fn new(kind: RuleAnnotationKind, restrictions: Vec<Operation>) -> Self {
        Self {
            origin: Origin::Created,
            id: ProgramComponentId::default(),
            kind,
            restrictions,
        }
    }

    /// Return the kind of the annotation
    pub fn kind(&self) -> RuleAnnotationKind {
        self.kind
    }

    /// Return the restrictions of the annotation
    pub fn restrictions(&self) -> &Vec<Operation> {
        &self.restrictions
    }

    /// Return a mutable reference to the operations as mut
    pub fn restrictions_mut(&mut self) -> &mut Vec<Operation> {
        &mut self.restrictions
    }

    /// Return the set of variables that are bound in the operations
    pub fn restricted_variables(&self) -> HashSet<&Variable> {
        self.restrictions
        .iter()
        .flat_map(|op| op.variables())
        .collect::<HashSet<_>>()
    }

}

impl ComponentBehavior for RuleAnnotation {
    fn kind(&self) -> ProgramComponentKind {
        ProgramComponentKind::RuleAnnotation
    }

    fn validate(&self) -> Result<(), ValidationReport> {
        todo!()
    }

    fn boxed_clone(&self) -> Box<dyn super::ProgramComponent> {
        Box::new(self.clone())
    }
}

impl ComponentSource for RuleAnnotation {
    type Source = Origin;

    fn origin(&self) -> Origin {
        self.origin.clone()
    }

    fn set_origin(&mut self, origin: Origin) {
        self.origin = origin;
    }
}

impl ComponentIdentity for RuleAnnotation {
    fn id(&self) -> ProgramComponentId {
        self.id
    }

    fn set_id(&mut self, id: ProgramComponentId) {
        self.id = id;
    }
}

impl IterableComponent for RuleAnnotation {
    fn children<'a>(&'a self) -> Box<dyn Iterator<Item = &'a dyn super::ProgramComponent> + 'a> {
        Box::new(component_iterator(self.restrictions.iter()))
    }

    fn children_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut dyn super::ProgramComponent> + 'a> {
        Box::new(component_iterator_mut(self.restrictions.iter_mut()))
    }
}

impl Display for RuleAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            RuleAnnotationKind::Requires => f.write_str("[requires ")?,
            RuleAnnotationKind::Ensures => f.write_str("[ensures ")?,
        }

        f.write_str(": ")?;
        for (index, op_literal) in self.restrictions.iter().enumerate() {
            write!(f, "{op_literal}")?;

            if index < self.restrictions.len() - 1 {
                f.write_str(", ")?;
            }
        }
        f.write_str("]")
    }
}


impl PartialEq for RuleAnnotation {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind &&  self.restrictions == other.restrictions
    }
}

impl Eq for RuleAnnotation {}

impl Hash for RuleAnnotation{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        self.restrictions.hash(state);
    }
}

impl IterableVariables for RuleAnnotation {
    fn variables<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Variable> + 'a> {
        Box::new(self.restrictions.iter().flat_map(|op| op.variables()))
    }
    
    fn variables_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Variable> + 'a> {
        Box::new(self.restrictions.iter_mut().flat_map(|op| op.variables_mut()))
    }
}
