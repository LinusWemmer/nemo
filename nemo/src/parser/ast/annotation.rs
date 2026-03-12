//! This module defines [Annotation].

use enum_assoc::Assoc;
use nom::{sequence::{delimited, pair, terminated, tuple}, branch::alt};

use crate::parser::{
    ParserResult, ast::{expression::complex::infix::{self, InfixExpression}, sequence::Sequence, token::TokenKind}, context::{ParserContext, context}, input::ParserInput, span::Span
};

use super::{ProgramAST, comment::wsoc::WSoC, expression::complex::atom::Atom, token::Token};

/// Types of Annotations
#[derive(Assoc, Debug, Copy, Clone, PartialEq, Eq)]
#[func(pub fn token(token: TokenKind) -> Option<Self>)]
pub enum AnnotationKind{
    /// Requires Annotation
    #[assoc(token = TokenKind::RequiresAnnotation)]
    Requires,
    /// Ensure Annotation
    #[assoc(token = TokenKind::EnsureAnnotation)]
    Ensure,
}

/// Rule Annotation
#[derive(Debug)]
pub struct Annotation<'a> {
    /// [Span] associated with this node
    span: Span<'a>,
    /// Annotation Kind, for now we only do requires
    kind: AnnotationKind,
    /// [Atom] containing the content of the directive
    content: Atom<'a>,
}

impl<'a> Annotation<'a> {
    /// Return the [Atom] that contains the content of the annotation
    pub fn content(&self) -> &Atom<'a> {
        &self.content
    }

    /// Return the [AnnotationKind] of this annotation
    pub fn kind(&self) -> &AnnotationKind{
        &self.kind
    }

    /// Parse an [AnnotationKind]
    pub fn parse_annotation_kind(input: ParserInput<'a>) -> ParserResult<'a, AnnotationKind> {
        alt((Token::requires_annotation,
            Token::ensures_annotation,
        ))(input)
        .map(|(rest, result)| {
            (
                rest,
                AnnotationKind::token(result.kind())
                    .unwrap_or_else(|| panic!("unexpected token: {:?}", result.kind())),
            )
        })
    }
}

const CONTEXT: ParserContext = ParserContext::Attribute;

impl<'a> ProgramAST<'a> for Annotation<'a> {
    fn children(&self) -> Vec<&dyn ProgramAST<'a>> {
        vec![self.content()]
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
            terminated(
                delimited(
                    tuple((Token::open_annotation, WSoC::parse)),
                    tuple((
                        Self::parse_annotation_kind,
                        WSoC::parse, Atom::parse,
                        Sequence::<InfixExpression>::parse
                    )),
                    pair(WSoC::parse, Token::close_annotation),
                ),
                WSoC::parse,
            ),
        )(input)
        .map(|(rest, (kind,_,content, _))| {
            let rest_span = rest.span;

            (
                rest,
                Self {
                    span: input_span.until_rest(&rest_span),
                    kind,
                    content,
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
        ast::{ProgramAST, annotation::{Annotation, AnnotationKind}},
        input::ParserInput,
    };

    #[test]
    fn parse_annotation() {
        let test = vec![
            ("[requires: test(?X, ?Y, ?Z)]\n", ("test".to_string(), 3, AnnotationKind::Requires)),
            ("[ensure: abc(1) ]\n", ("abc".to_string(), 1, AnnotationKind::Ensure)),
        ];

        for (input, expected) in test {
            let parser_input = ParserInput::new(input, ParserState::default());
            let result = all_consuming(Annotation::parse)(parser_input);

            assert!(result.is_ok());

            let result = result.unwrap();
            println!("");
            assert_eq!(
                expected,
                (
                    result.1.content.tag().to_string(),
                    result.1.content.expressions().count(),
                    result.1.kind
                )
            );
        }
    }
}
