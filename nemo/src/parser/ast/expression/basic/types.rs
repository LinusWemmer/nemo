//! This module defines [Variable]
#![allow(missing_docs)]

use enum_assoc::Assoc;
use nom::{
    branch::alt,
    combinator::map,
};

use crate::parser::{
    ParserResult,
    ast::{
        ProgramAST,
        token::{Token, TokenKind},
    },
    context::{ParserContext, context},
    input::ParserInput,
    span::Span,
};

/// Marker that indicates the type of variable
#[derive(Assoc, Debug, Clone, Copy, PartialEq, Eq)]
#[func(pub fn token(token: TokenKind) -> Option<Self>)]
pub enum Sort{
    /// Universal variable
    #[assoc(token = TokenKind::TypeIndicatorInt)]
    TypeInt,
    /// Existential variable
    #[assoc(token = TokenKind::TypeIndicatorFloat)]
    TypeFloat,
    /// Global variable
    #[assoc(token = TokenKind::TypeIndicatorString)]
    TypeString,
    /// Anonymous variable
    #[assoc(token = TokenKind::AnonVal)]
    TypeAnonymous,
}

/// AST node representing a variable
#[derive(Debug)]
pub struct TypeLiteral<'a> {
    /// [Span] associated with this node
    span: Span<'a>,

    /// Type of variable
    sort: Sort,
}

impl<'a> TypeLiteral<'a> {

    /// Return the type of variable
    pub fn sort(&self) -> Sort {
        self.sort
    }

    /// Parse a named variable
    fn parse_type(input: ParserInput<'a>) -> ParserResult<'a, Sort> {

        map(
            alt((
                Token::type_indicator_int,
                Token::type_indicator_float,
                Token::type_indicator_strig
            )),
            |indicator| {
                Sort::token(indicator.kind()).expect("unknown variable indicator")
            },
        )(input)
    }

    /// Parse an anonymous variable
    fn parse_anonymous_type(input: ParserInput<'a>) -> ParserResult<'a, Sort> {
        map(Token::underscore, |indicator| {
            Sort::token(indicator.kind()).expect("unknown variable indicator")
        })(input)
    }
}

const CONTEXT: ParserContext = ParserContext::Variable;

impl<'a> ProgramAST<'a> for TypeLiteral<'a> {
    fn children(&self) -> Vec<&dyn ProgramAST<'a>> {
        Vec::default()
    }

    fn span(&self) -> Span<'a> {
        self.span
    }

    fn parse(input: ParserInput<'a>) -> ParserResult<'a, Self>
    where
        Self: Sized + 'a,
    {
        let input_span = input.span;

        context(
            CONTEXT,
            alt((
                map(Self::parse_type, |typ| typ),
                map(Self::parse_anonymous_type, |typ| typ),
            )),
        )(input)
        .map(|(rest, sort)| {
            let rest_span = rest.span;

            (
                rest,
                TypeLiteral {
                    span: input_span.until_rest(&rest_span),
                    sort,
                },
            )
        })
    }

    fn context(&self) -> ParserContext {
        CONTEXT
    }
}

#[cfg(test)]
mod test {
    use nom::combinator::all_consuming;
    use std::assert_matches;

    use crate::parser::{
        ParserState,
        ast::{ProgramAST, expression::basic::types::TypeLiteral},
        input::ParserInput,
    };

    use super::Sort;

    #[test]
    fn parse_type_literal() {
        let test = vec![
            (
                "int",
                (Sort::TypeInt),
            ),
            (
                "str",
                (Sort::TypeString),
            ),
        ];

        for (input, expected) in test {
            let parser_input = ParserInput::new(input, ParserState::default());
            let result = all_consuming(TypeLiteral::parse)(parser_input);

            assert_matches!(result, Ok(_));

            let result = result.unwrap();
            assert_eq!(expected, (result.1.sort()));
        }
    }
}
