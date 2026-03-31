//! This module defines [RuleAnnotation].
#![allow(missing_docs)]

use nom::{sequence::{delimited, pair, terminated, tuple}};

use crate::parser::{
    ParserResult, ast::{expression::complex::infix::InfixExpression, sequence::Sequence}, context::{ParserContext, context}, input::ParserInput, span::Span
};

use super::{ProgramAST, comment::wsoc::WSoC, token::Token};


/// An annotation that restricts variable ranges for rules
#[derive(Debug)]
pub struct RuleAnnotation<'a> {
    /// [Span] associated with this node
    span: Span<'a>,
    /// [Sequence] containing variable body
    body: Sequence<'a, InfixExpression<'a>>,
}

impl<'a> RuleAnnotation<'a> {
    /// Return the [Atom] that contains the content of the annotation
    pub fn body(&self) -> impl Iterator<Item = &InfixExpression<'a>> {
        self.body.iter()
    }
}

const CONTEXT: ParserContext = ParserContext::RuleAnnotation;

impl<'a> ProgramAST<'a> for RuleAnnotation<'a> {
    fn children(&self) -> Vec<&dyn ProgramAST<'a>> {
        let mut result = Vec::<&dyn ProgramAST>::new();

        for expression in self.body(){
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
                    Sequence::<InfixExpression>::parse,
                    pair(WSoC::parse, Token::close_rule_annotation),
                ),
                WSoC::parse,
            ),
        )(input)
        .map(|(rest, body)| {
            let rest_span = rest.span;

            (
                rest,
                Self {
                    span: input_span.until_rest(&rest_span),
                    body,
                },
            )
        })
    }

    //TODO: look at this
    fn context(&self) -> ParserContext {
        CONTEXT
    }
}

#[cfg(test)]
mod test {
    use nom::combinator::all_consuming;

    use crate::parser::{
        ParserState,
        ast::{ProgramAST, rule_annotation::RuleAnnotation},
        input::ParserInput,
    };

    #[test]
    fn parse_annotation() {
        let test = vec![
            ("[assert: 0<?X, ?X<5]\n"),
            ("[assert: ?X<?Y]\n"),
        ];

        for input in test {
            let parser_input = ParserInput::new(input, ParserState::default());
            let result = all_consuming(RuleAnnotation::parse)(parser_input);

            assert!(result.is_ok());
        }
    }
}
