//! This module contains functions to translate ast nodes into global annotations

use crate::{
    parser::ast::{self, global_annotation::GlobalAnnotationKind},
    rule_model::{
        components::{self, atom::Atom, global_annotation::GlobalAnnotation, tag::Tag, term::{Term, operation::Operation}},
        origin::Origin, translation::complex::infix::InfixOperation,
    },
};

use super::TranslationComponent;

impl TranslationComponent for GlobalAnnotation {
    type Ast<'a> = ast::global_annotation::GlobalAnnotation<'a>;

    fn build_component<'a>(
        translation: &mut super::ASTProgramTranslation,
        annotation: &Self::Ast<'a>,
    ) -> Option<Self> {
        
        //TODO: move the annotationkind to be a shared enum
        let kind = match annotation.kind(){ 
          GlobalAnnotationKind::Assert => components::global_annotation::GlobalAnnotationKind::Assert,
          GlobalAnnotationKind::Verify => components::global_annotation::GlobalAnnotationKind::Assert
        };
        //  Build the restricted atom:
        let atom = annotation.predicate();
        let tag =
            Origin::ast(Tag::from(translation.resolve_tag(atom.tag())?), atom.tag());
        let mut subterms = Vec::new();
        for expression in atom.expressions() {
            subterms.push(Term::build_component(translation, expression)?);
        }
        let predicate = Origin::ast(Atom::new(tag, subterms), atom);

        // Build the restrictions:
        let mut restrictions: Vec<Operation> = Vec::default();
        for expression in annotation.restrictions() {
            restrictions.push(InfixOperation::build_component(translation, expression)?.into_inner());
        }


        Some(Origin::ast(GlobalAnnotation::new(kind, predicate, restrictions), annotation))
    }
}