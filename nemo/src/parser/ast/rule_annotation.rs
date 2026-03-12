//! This module defines [RuleAnnotation].

use enum_assoc::Assoc;
use nom::{sequence::{delimited, pair, terminated, tuple}, branch::alt};

use crate::parser::{
    ParserResult, ast::{expression::complex::infix::InfixExpression, sequence::Sequence, token::TokenKind}, context::{ParserContext, context}, input::ParserInput, span::Span
};

use super::{ProgramAST, comment::wsoc::WSoC, token::Token};

/// Types of Annotations
#[derive(Assoc, Debug, Copy, Clone, PartialEq, Eq)]
#[func(pub fn token(token: TokenKind) -> Option<Self>)]
pub enum RuleAnnotationKind{
    /// Requires RuleAnnotation
    #[assoc(token = TokenKind::RequiresAnnotation)]
    Requires,
    /// Ensure RuleAnnotation
    #[assoc(token = TokenKind::EnsureAnnotation)]
    Ensure,
}

/// Rule RuleAnnotation, i.e. on variables in rule , WIP
#[derive(Debug)]
pub struct RuleAnnotation<'a> {
    /// [Span] associated with this node
    span: Span<'a>,
    /// RuleAnnotation Kind, for now we only do requires
    kind: RuleAnnotationKind,
    /// [Sequence] containing variable restrictions
    restriction: Sequence<'a, InfixExpression<'a>>,
}

impl<'a> RuleAnnotation<'a> {
    /// Return the [Atom] that contains the content of the annotation
    pub fn restriction(&self) -> impl Iterator<Item = &InfixExpression<'a>> {
        self.restriction.iter()
    }

    /// Return the [AnnotationKind] of this annotation
    pub fn kind(&self) -> &RuleAnnotationKind{
        &self.kind
    }

    /// Parse an [AnnotationKind]
    pub fn parse_annotation_kind(input: ParserInput<'a>) -> ParserResult<'a, RuleAnnotationKind> {
        alt((Token::requires_annotation,
            Token::ensures_annotation,
        ))(input)
        .map(|(rest, result)| {
            (
                rest,
                RuleAnnotationKind::token(result.kind())
                    .unwrap_or_else(|| panic!("unexpected token: {:?}", result.kind())),
            )
        })
    }
}

const CONTEXT: ParserContext = ParserContext::RuleAnnotation;

impl<'a> ProgramAST<'a> for RuleAnnotation<'a> {
    fn children(&self) -> Vec<&dyn ProgramAST<'a>> {
        let mut result = Vec::<&dyn ProgramAST>::new();

        for expression in self.restriction(){
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
        // TODO: make annotation into seperated pair (by ":")
        context(
            CONTEXT,
            terminated(
                delimited(
                    tuple((Token::open_rule_annotation, WSoC::parse)),
                    tuple((Self::parse_annotation_kind, WSoC::parse, Sequence::<InfixExpression>::parse)),
                    pair(WSoC::parse, Token::close_rule_annotation),
                ),
                WSoC::parse,
            ),
        )(input)
        .map(|(rest, (kind,_,restriction))| {
            let rest_span = rest.span;

            (
                rest,
                Self {
                    span: input_span.until_rest(&rest_span),
                    kind,
                    restriction,
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
        ast::{ProgramAST, rule_annotation::{RuleAnnotation, RuleAnnotationKind}},
        input::ParserInput,
    };

    #[test]
    fn parse_annotation() {
        let test = vec![
            ("[requires: 0<?X, ?X<5]\n", (RuleAnnotationKind::Requires)),
            ("[ensure: ?X<?Y]\n", (RuleAnnotationKind::Ensure)),
        ];

        for (input, expected) in test {
            let parser_input = ParserInput::new(input, ParserState::default());
            let result = all_consuming(RuleAnnotation::parse)(parser_input);

            assert!(result.is_ok());

            let result = result.unwrap();
            println!("");
            assert_eq!(
                expected,
                (
                    result.1.kind
                )
            );
        }
    }
}
