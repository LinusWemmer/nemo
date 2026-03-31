//! This module contains functions to translate ast nodes into rule annotations

use crate::{
    parser::ast::{self},
    rule_model::{
        components::{rule_annotation::RuleAnnotation, term::operation::Operation},
        origin::Origin, translation::complex::infix::InfixOperation,
    },
};

use super::TranslationComponent;

pub(crate) fn process_annotations<'a>(
    translation: &mut super::ASTProgramTranslation,
    annotations: impl Iterator<Item = &'a ast::rule_annotation::RuleAnnotation<'a>>,
) -> Option<Vec<RuleAnnotation>> {

    let mut result: Vec<RuleAnnotation> = Vec::new();

    for annotation in annotations{

      let mut body: Vec<Operation> = Vec::default();
        for expression in annotation.body() {
            body.push(InfixOperation::build_component(translation, expression)?.into_inner());
        }
        
      result.push(Origin::ast(RuleAnnotation::new(body), annotation));
    }
    
    Some(result)
} 