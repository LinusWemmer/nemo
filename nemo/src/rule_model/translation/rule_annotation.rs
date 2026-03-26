//! This module contains functions to translate ast nodes into rule annotations

use crate::{
    parser::ast::{self, rule_annotation::RuleAnnotationKind},
    rule_model::{
        components::{self, rule_annotation::RuleAnnotation, term::operation::Operation},
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

      let kind = match annotation.kind(){ 
          RuleAnnotationKind::Requires => components::rule_annotation::RuleAnnotationKind::Requires,
          RuleAnnotationKind::Ensure  => components::rule_annotation::RuleAnnotationKind::Ensures,
      };

      let mut restrictions: Vec<Operation> = Vec::default();
        for expression in annotation.restriction() {
            restrictions.push(InfixOperation::build_component(translation, expression)?.into_inner());
        }
        
      result.push(Origin::ast(RuleAnnotation::new(kind, restrictions), annotation));
    }
    
    Some(result)
} 