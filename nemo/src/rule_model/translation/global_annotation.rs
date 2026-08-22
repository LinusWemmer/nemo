//! This module contains functions to translate ast nodes into global annotations

use crate::{
    parser::ast::{self},
    rule_model::{
        components::{
            atom::Atom,
            global_annotation::GlobalAnnotation,
            tag::Tag,
            term::{Term, operation::Operation},
        },
        origin::Origin,
        translation::complex::infix::InfixOperation,
    },
};

use super::TranslationComponent;

impl TranslationComponent for GlobalAnnotation {
    type Ast<'a> = ast::global_annotation::GlobalAnnotation<'a>;

    fn build_component<'a>(
        translation: &mut super::ASTProgramTranslation,
        annotation: &Self::Ast<'a>,
    ) -> Option<Self> {
        //  Build the restricted atom:
        let atom = annotation.predicate();
        let tag = Origin::ast(Tag::from(translation.resolve_tag(atom.tag())?), atom.tag());
        let mut subterms = Vec::new();
        for expression in atom.expressions() {
            subterms.push(Term::build_component(translation, expression)?);
        }
        let predicate = Origin::ast(Atom::new(tag, subterms), atom);

        // Build the body:
        let mut body: Vec<Operation> = Vec::default();
        for expression in annotation.body() {
            body.push(InfixOperation::build_component(translation, expression)?.into_inner());
        }

        Some(Origin::ast(
            GlobalAnnotation::new(predicate, body),
            annotation,
        ))
    }
}
