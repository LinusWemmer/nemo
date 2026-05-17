//! This module contains functions to translate ast nodes into global annotations

use crate::{
    parser::ast::{self},
    rule_model::{
        components::{tag::Tag, type_annotation::{self, TypeAnnotation}},
        origin::Origin,
    },
};

use super::TranslationComponent;

impl TranslationComponent for TypeAnnotation {
    type Ast<'a> = ast::type_annotation::TypeAnnotation<'a>;

    fn build_component<'a>(
        translation: &mut super::ASTProgramTranslation,
        types: &Self::Ast<'a>,
    ) -> Option<Self> {
        let predicate =
            Origin::ast(Tag::from(translation.resolve_tag(types.tag())?), types.tag());
        let mut sorts = types.body().map(|lit|{
            match lit.sort(){
                ast::expression::basic::types::Sort::TypeInt => 
                    type_annotation::Sort::TypeInt,
                ast::expression::basic::types::Sort::TypeFloat => 
                    type_annotation::Sort::TypeFloat,
                ast::expression::basic::types::Sort::TypeString => 
                    type_annotation::Sort::TypeString,
                ast::expression::basic::types::Sort::TypeAnonymous => 
                    type_annotation::Sort::TypeAnonymous,
            }
        }).collect();

        Some(Origin::ast(TypeAnnotation::new(predicate, sorts), types))
    }
}