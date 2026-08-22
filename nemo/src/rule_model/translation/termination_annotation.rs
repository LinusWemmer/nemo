//! This module contains functions to translate ast nodes into termination annotations

use crate::{
    parser::ast::{self},
    rule_model::{
        self,
        components::{
            atom::Atom,
            tag::Tag,
            term::{Term, primitive::variable::Variable},
            termination_annotation::TerminationAnnotation,
        },
        origin::Origin,
        translation::complex::arithmetic::ArithmeticOperation,
    },
};

use super::TranslationComponent;

impl TranslationComponent for TerminationAnnotation {
    type Ast<'a> = ast::termination_annotation::TerminationAnnotation<'a>;

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

        let direction = match annotation.kind() {
            ast::termination_annotation::TerminationDirection::Decreasing => {
                rule_model::components::termination_annotation::TerminationDirection::Decreasing
            }
            ast::termination_annotation::TerminationDirection::Increasing => {
                rule_model::components::termination_annotation::TerminationDirection::Increasing
            }
        };

        // Build the body:
        let body = match annotation.body() {
            ast::expression::Expression::Arithmetic(arithmetic) => Term::from(
                ArithmeticOperation::build_component(translation, arithmetic)?.into_inner(),
            ),
            ast::expression::Expression::Variable(variable) => {
                Term::from(Variable::build_component(translation, variable)?)
            }
            _ => panic!(
                "Only arithmetic expressions and variables are allowed in termination annotation"
            ),
        };
        Some(Origin::ast(
            TerminationAnnotation::new(predicate, body, direction),
            annotation,
        ))
    }
}
