//! This module defines [GlobalAnnotation].
#![allow(missing_docs)]

use enum_assoc::Assoc;
use nom::{branch::alt, sequence::{separated_pair, tuple}};

use crate::parser::{
    ParserResult, ast::{expression::complex::{infix::InfixExpression, atom::Atom}, sequence::Sequence, token::TokenKind}, context::{ParserContext, context}, input::ParserInput, span::Span
};

use super::{ProgramAST, comment::wsoc::WSoC, token::Token};

/// Types of Annotations TODO: probably open assert should be changed to differentiate between start and kind?
#[derive(Assoc, Debug, Copy, Clone, PartialEq, Eq)]
#[func(pub fn token(token: TokenKind) -> Option<Self>)]
pub enum GlobalAnnotationKind{
    /// Requires GlobalAnnotation
    #[assoc(token = TokenKind::OpenAssert)]
    Assert,
    /// Ensure GlobalAnnotation
    #[assoc(token = TokenKind::OpenVerify)]
    Verify,
}

/// An annotation that restricts variable ranges for rules
#[derive(Debug)]
pub struct GlobalAnnotation<'a> {
    /// [Span] associated with this node
    span: Span<'a>,
    /// GlobalAnnotation Kind, for now we only do requires
    kind: GlobalAnnotationKind,
    /// Atom to be restricted
    predicate: Atom<'a>,
    /// [Sequence] containing variable restrictions
    restrictions: Sequence<'a, InfixExpression<'a>>,
}

impl<'a> GlobalAnnotation<'a> {
    /// Return the restrictions of the global annotation
    pub fn restrictions(&self) -> impl Iterator<Item = &InfixExpression<'a>> {
        self.restrictions.iter()
    }

    /// Return the [AnnotationKind] of this annotation
    pub fn kind(&self) -> &GlobalAnnotationKind{
        &self.kind
    }

    /// Return the [Atom] that is annotated
    pub fn predicate(&self) -> &Atom<'a>{
        &self.predicate
    }

    /// Parse an [AnnotationKind]
    pub fn parse_annotation_kind(input: ParserInput<'a>) -> ParserResult<'a, GlobalAnnotationKind> {
        alt((
            Token::open_assert,
            Token::open_verify,
        ))(input)
        .map(|(rest, result)| {
            (
                rest,
                GlobalAnnotationKind::token(result.kind())
                    .unwrap_or_else(|| panic!("unexpected token: {:?}", result.kind())),
            )
        })
    }
}

const CONTEXT: ParserContext = ParserContext::GlobalAnnotation;

impl<'a> ProgramAST<'a> for GlobalAnnotation<'a> {
    fn children(&self) -> Vec<&dyn ProgramAST<'a>> {
        let mut result = Vec::<&dyn ProgramAST>::new();

        for expression in self.restrictions(){
            result.push(expression);
        }

        result
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
                separated_pair(
                    tuple((Self::parse_annotation_kind, WSoC::parse, Atom::parse)),
                    tuple((WSoC::parse, Token::annotation_seperator, WSoC::parse)),
                    Sequence::<InfixExpression>::parse,
                ),
        )(input)
        .map(|(rest, ((kind, _, predicate), restrictions) )| {
            let rest_span = rest.span;

            (
                rest,
                Self {
                    span: input_span.until_rest(&rest_span),
                    kind,
                    predicate,
                    restrictions,
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

    use crate::parser::{
        ParserState,
        ast::{ProgramAST, global_annotation::{GlobalAnnotation, GlobalAnnotationKind}},
        input::ParserInput,
    };

    #[test]
    fn parse_annotation() {
        let test = vec![
            ("#assert test(?X,?Y): ?X<3", ("test".to_string(), GlobalAnnotationKind::Assert)),
            ("#verify bla(?X):  0<?X, ?X<10", ("bla".to_string(), GlobalAnnotationKind::Verify)),
        ];

        for (input, expected) in test {
            let parser_input = ParserInput::new(input, ParserState::default());
            let result = all_consuming(GlobalAnnotation::parse)(parser_input);

            assert!(result.is_ok());

            let result = result.unwrap();
            println!("");
            assert_eq!(
                expected,
                (
                    result.1.predicate.tag().to_string(),
                    result.1.kind
                )
            );
        }
    }
}
