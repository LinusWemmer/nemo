//! This module defines [Global_Annotation].

use std::{fmt::Display, hash::Hash};

use nemo_physical::datavalues::ValueDomain;

use crate::rule_model::{
    components::{IterablePrimitives, IterableVariables, tag::Tag},
    error::ValidationReport,
    origin::Origin,
    pipeline::id::ProgramComponentId,
};

use super::{
    ComponentBehavior, ComponentIdentity, ComponentSource, IterableComponent, ProgramComponentKind,
};

#[derive(Debug, Clone)]
pub struct TypeAnnotation {
    /// Origin of this component
    origin: Origin,
    /// Id of this component
    id: ProgramComponentId,
    /// predicate of the annotation
    predicate: Tag,
    /// sorts of the annotation
    sorts: Vec<ValueDomain>,
}

impl TypeAnnotation {
    /// Create a new [TypeAnnotation].
    pub fn new(predicate: Tag, sorts: Vec<ValueDomain>) -> Self {
        Self {
            origin: Origin::Created,
            id: ProgramComponentId::default(),
            predicate,
            sorts,
        }
    }

    /// Return a reference to the predicate that is annotated
    pub fn predicate(&self) -> &Tag {
        &self.predicate
    }

    /// Return the sorts of the operations
    pub fn sorts(&self) -> &Vec<ValueDomain> {
        &self.sorts
    }

    /// Return a mutable reference to the operations as mut
    pub fn sorts_mut(&mut self) -> &mut Vec<ValueDomain> {
        &mut self.sorts
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

impl IterableComponent for TypeAnnotation {
    fn children<'a>(&'a self) -> Box<dyn Iterator<Item = &'a dyn super::ProgramComponent> + 'a> {
        Box::new(std::iter::empty())
    }

    fn children_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut dyn super::ProgramComponent> + 'a> {
        Box::new(std::iter::empty())
    }
}

impl IterableVariables for TypeAnnotation {
    fn variables<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = &'a super::term::primitive::variable::Variable> + 'a> {
        Box::new(std::iter::empty())
    }

    fn variables_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut super::term::primitive::variable::Variable> + 'a> {
        Box::new(std::iter::empty())
    }
}

impl IterablePrimitives for TypeAnnotation {
    type TermType = super::term::Term;

    fn primitive_terms<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = &'a super::term::primitive::Primitive> + 'a> {
        Box::new(std::iter::empty())
    }

    fn primitive_terms_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut Self::TermType> + 'a> {
        Box::new(std::iter::empty())
    }
}

impl Display for TypeAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("#type ")?;
        let pred = &self.predicate.to_string();
        write!(f, "{pred} ( ")?;

        for (index, sort) in self.sorts.iter().enumerate() {
            match sort {
                ValueDomain::PlainString => write!(f, "string")?,
                ValueDomain::LanguageTaggedString => write!(f, "language-tagged string")?,
                ValueDomain::Iri => write!(f, "iri")?,
                ValueDomain::Float => write!(f, "float")?,
                ValueDomain::Double => write!(f, "double")?,
                ValueDomain::UnsignedLong => write!(f, "unsigned long")?,
                ValueDomain::NonNegativeLong => write!(f, "non-negative long")?,
                ValueDomain::UnsignedInt => write!(f, "unsigned int")?,
                ValueDomain::NonNegativeInt => write!(f, "non-negative int")?,
                ValueDomain::Long => write!(f, "long")?,
                ValueDomain::Int => write!(f, "int")?,
                ValueDomain::Tuple => write!(f, "tuple")?,
                ValueDomain::Map => write!(f, "map")?,
                ValueDomain::Boolean => write!(f, "boolean")?,
                ValueDomain::Null => write!(f, "null")?,
                ValueDomain::Other => write!(f, "other")?,
            }

            if index < self.sorts.len() - 1 {
                f.write_str(", ")?;
            }
        }
        f.write_str(").")
    }
}

impl PartialEq for TypeAnnotation {
    fn eq(&self, other: &Self) -> bool {
        self.predicate == other.predicate && self.sorts == other.sorts
    }
}

impl Eq for TypeAnnotation {}

impl Hash for TypeAnnotation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.predicate.hash(state);
        self.sorts.hash(state);
    }
}
