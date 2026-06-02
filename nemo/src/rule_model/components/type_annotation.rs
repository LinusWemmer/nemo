//! This module defines [Global_Annotation].

use std::{fmt::Display, hash::Hash};

use crate::rule_model::{
    components::tag::Tag, error::ValidationReport, origin::Origin, pipeline::id::ProgramComponentId,
};

use super::{
    ComponentBehavior, ComponentIdentity, ComponentSource, IterableComponent, ProgramComponentKind,
};

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

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::TypeInt => write!(f, "int"),
            Sort::TypeFloat => write!(f, "float"),
            Sort::TypeString => write!(f, "str"),
            Sort::TypeAnonymous => write!(f, "_"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeAnnotation {
    /// Origin of this component
    origin: Origin,
    /// Id of this component
    id: ProgramComponentId,
    /// predicate of the annotation
    predicate: Tag,
    /// body of the annotation
    body: Vec<Sort>,
}

impl TypeAnnotation {
    /// Create a new [TypeAnnotation].
    pub fn new(predicate: Tag, body: Vec<Sort>) -> Self {
        Self {
            origin: Origin::Created,
            id: ProgramComponentId::default(),
            predicate,
            body,
        }
    }

    /// Return a reference to the predicate that is annotated
    pub fn predicate(&self) -> &Tag {
        &self.predicate
    }

    /// Return the body of the operations
    pub fn body(&self) -> &Vec<Sort> {
        &self.body
    }

    /// Return a mutable reference to the operations as mut
    pub fn body_mut(&mut self) -> &mut Vec<Sort> {
        &mut self.body
    }
}

impl ComponentBehavior for TypeAnnotation {
    fn kind(&self) -> ProgramComponentKind {
        ProgramComponentKind::TypeAnnotation
    }

    /// Validate the type annotation
    fn validate(&self) -> Result<(), ValidationReport> {
        ValidationReport::default().result()
    }

    fn boxed_clone(&self) -> Box<dyn super::ProgramComponent> {
        Box::new(self.clone())
    }
}

impl ComponentSource for TypeAnnotation {
    type Source = Origin;

    fn origin(&self) -> Origin {
        self.origin.clone()
    }

    fn set_origin(&mut self, origin: Origin) {
        self.origin = origin;
    }
}

impl ComponentIdentity for TypeAnnotation {
    fn id(&self) -> ProgramComponentId {
        self.id
    }

    fn set_id(&mut self, id: ProgramComponentId) {
        self.id = id;
    }
}

impl IterableComponent for TypeAnnotation {}

impl Display for TypeAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#type ")?;
        let pred = &self.predicate.to_string();
        write!(f, "{pred} ( ")?;

        for (index, op_literal) in self.body.iter().enumerate() {
            write!(f, "{op_literal}")?;

            if index < self.body.len() - 1 {
                f.write_str(", ")?;
            }
        }
        f.write_str(").")
    }
}

impl PartialEq for TypeAnnotation {
    fn eq(&self, other: &Self) -> bool {
        self.predicate == other.predicate && self.body == other.body
    }
}

impl Eq for TypeAnnotation {}

impl Hash for TypeAnnotation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.predicate.hash(state);
        self.body.hash(state);
    }
}
