//! This module defines [TerminationAnnotation].
#![allow(missing_docs)]

use enum_assoc::Assoc;
use nom::{
    branch::alt,
    sequence::{separated_pair, tuple},
};

use crate::parser::{
    ParserResult,
    ast::{
        expression::{Expression, complex::atom::Atom},
        token::TokenKind,
    },
    context::{ParserContext, context},
    input::ParserInput,
    span::Span,
};

use super::{ProgramAST, comment::wsoc::WSoC, token::Token};

#[derive(Assoc, Debug, Clone, Copy, PartialEq, Eq)]
#[func(pub fn token(token: TokenKind) -> Option<Self>)]
pub enum TerminationDirection {
    #[assoc(token = TokenKind::OpenDecrease)]
    Decreasing,
    #[assoc(token = TokenKind::OpenIncrease)]
    Increasing,
}

/// An annotation that restricts variable ranges for rules
#[derive(Debug)]
pub struct TerminationAnnotation<'a> {
    /// [Span] associated with this node
    span: Span<'a>,
    /// Atom to be restricted
    predicate: Atom<'a>,
    /// In which direction does the change happen
    direction: TerminationDirection,
    /// Function for the annotation
    body: Expression<'a>,
}

impl<'a> TerminationAnnotation<'a> {
    /// Return the body of the annotation
    pub fn body(&self) -> &Expression<'a> {
        &self.body
    }

    /// Return the [Atom] that is annotated
    pub fn predicate(&self) -> &Atom<'a> {
        &self.predicate
    }

    /// Returns the [TerminationDirection]
    pub fn kind(&self) -> &TerminationDirection {
        &self.direction
    }
}

const CONTEXT: ParserContext = ParserContext::TerminationAnnotation;

impl<'a> ProgramAST<'a> for TerminationAnnotation<'a> {
    fn children(&self) -> Vec<&dyn ProgramAST<'a>> {
        let mut result = Vec::<&dyn ProgramAST>::new();

        result.push(self.body());

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
                tuple((
                    alt((Token::open_increase, Token::open_decrease)),
                    WSoC::parse,
                    Atom::parse,
                )),
                tuple((WSoC::parse, Token::annotation_seperator, WSoC::parse)),
                Expression::parse,
            ),
        )(input)
        .map(|(rest, ((token, _, predicate), body))| {
            let rest_span = rest.span;
            let direction = TerminationDirection::token(token.kind())
                .expect("unrecogniszed annotation direction");
            (
                rest,
                Self {
                    span: input_span.until_rest(&rest_span),
                    predicate,
                    direction,
                    body,
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
        ast::{ProgramAST, termination_annotation::TerminationAnnotation},
        input::ParserInput,
    };

    #[test]
    fn parse_annotation() {
        let test = vec![
            ("#decreases test(?X,?Y): ?X + ?Y", ("test".to_string())),
            ("#increases bla(?Z):  ?Z+0", ("bla".to_string())),
        ];

        for (input, expected) in test {
            let parser_input = ParserInput::new(input, ParserState::default());
            let result = all_consuming(TerminationAnnotation::parse)(parser_input);

            assert!(result.is_ok());

            let result = result.unwrap();

            assert_eq!(result.1.predicate.tag().to_string(), expected);
        }
    }
}
