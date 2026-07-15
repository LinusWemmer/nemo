//! This module contains functions to translate ast nodes into global annotations

use crate::{
    parser::ast::{self},
    rule_model::{
        components::{tag::Tag, type_annotation::TypeAnnotation},
        origin::Origin,
    },
};

use nemo_physical::datavalues::ValueDomain;

use super::TranslationComponent;

impl TranslationComponent for TypeAnnotation {
    type Ast<'a> = ast::type_annotation::TypeAnnotation<'a>;

    fn build_component<'a>(
        translation: &mut super::ASTProgramTranslation,
        types: &Self::Ast<'a>,
    ) -> Option<Self> {
        let predicate = Origin::ast(
            Tag::from(translation.resolve_tag(types.tag())?),
            types.tag(),
        );
        let sorts = types
            .body()
            .map(|lit| match lit.sort() {
                ast::expression::basic::types::Sort::TypeInt => ValueDomain::Int,
                ast::expression::basic::types::Sort::TypeFloat => ValueDomain::Float,
                ast::expression::basic::types::Sort::TypeString => ValueDomain::PlainString,
                ast::expression::basic::types::Sort::TypeLanguageTaggedString => {
                    ValueDomain::LanguageTaggedString
                }
                ast::expression::basic::types::Sort::TypeIri => ValueDomain::Iri,
                ast::expression::basic::types::Sort::TypeDouble => ValueDomain::Double,
                ast::expression::basic::types::Sort::TypeUnsignedLong => ValueDomain::UnsignedLong,
                ast::expression::basic::types::Sort::TypeNonNegativeLong => {
                    ValueDomain::NonNegativeLong
                }
                ast::expression::basic::types::Sort::TypeUnsignedInt => ValueDomain::UnsignedInt,
                ast::expression::basic::types::Sort::TypeNonNegativeInt => {
                    ValueDomain::NonNegativeInt
                }
                ast::expression::basic::types::Sort::TypeLong => ValueDomain::Long,
                ast::expression::basic::types::Sort::TypeTuple => ValueDomain::Tuple,
                ast::expression::basic::types::Sort::TypeMap => ValueDomain::Map,
                ast::expression::basic::types::Sort::TypeBoolean => ValueDomain::Boolean,
                ast::expression::basic::types::Sort::TypeNull => ValueDomain::Null,
                ast::expression::basic::types::Sort::TypeOther => ValueDomain::Other,
            })
            .collect();

        Some(Origin::ast(TypeAnnotation::new(predicate, sorts), types))
    }
}
