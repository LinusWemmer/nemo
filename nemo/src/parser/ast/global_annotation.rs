//! This module defines [GlobalAnnotation].
#![allow(missing_docs)]

use nom::sequence::{separated_pair, tuple};

use crate::parser::{
    ParserResult, ast::{expression::complex::{infix::InfixExpression, atom::Atom}, sequence::Sequence}, context::{ParserContext, context}, input::ParserInput, span::Span
};

use super::{ProgramAST, comment::wsoc::WSoC, token::Token};

/// An annotation that restricts variable ranges for rules
#[derive(Debug)]
pub struct GlobalAnnotation<'a> {
    /// [Span] associated with this node
    span: Span<'a>,
    /// Atom to be restricted
    predicate: Atom<'a>,
    /// [Sequence] containing variable body
    body: Sequence<'a, InfixExpression<'a>>,
}

impl<'a> GlobalAnnotation<'a> {
    /// Return the body of the global annotation
    pub fn body(&self) -> impl Iterator<Item = &InfixExpression<'a>> {
        self.body.iter()
    }

    /// Return the [Atom] that is annotated
    pub fn predicate(&self) -> &Atom<'a>{
        &self.predicate
    }
}

const CONTEXT: ParserContext = ParserContext::GlobalAnnotation;

impl<'a> ProgramAST<'a> for GlobalAnnotation<'a> {
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
        context(
            CONTEXT,
                separated_pair(
                    tuple((Token::open_assert, WSoC::parse, Atom::parse)),
                    tuple((WSoC::parse, Token::annotation_seperator, WSoC::parse)),
                    Sequence::<InfixExpression>::parse,
                ),
        )(input)
        .map(|(rest, ((_,_,predicate), body) )| {
            let rest_span = rest.span;

            (
                rest,
                Self {
                    span: input_span.until_rest(&rest_span),
                    predicate,
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
        ast::{ProgramAST, global_annotation::GlobalAnnotation},
        input::ParserInput,
    };

    #[test]
    fn parse_annotation() {
        let test = vec![
            ("#assert test(?X,?Y): ?X<3", ("test".to_string())),
            ("#assert bla(?X):  0<?X, ?X<10", ("bla".to_string())),
        ];

        for (input, expected) in test {
            let parser_input = ParserInput::new(input, ParserState::default());
            let result = all_consuming(GlobalAnnotation::parse)(parser_input);

            assert!(result.is_ok());

            let result = result.unwrap();
            println!("");
            assert_eq!(result.1.predicate.tag().to_string(), expected);
        }
    }
}
