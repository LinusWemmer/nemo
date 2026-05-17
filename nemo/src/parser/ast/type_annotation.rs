//! This module defines [TypeAnnotation].
#![allow(missing_docs)]

use nom::sequence::{tuple, pair, delimited};

use crate::parser::{
    ParserResult, ast::{
        expression::basic::types::TypeLiteral,
            sequence::type_lit::TypeLiteralSequence, tag::structure::StructureTag
        },
    context::{ParserContext, context}, input::ParserInput, span::Span
};

use super::{ProgramAST, comment::wsoc::WSoC, token::Token};

/// An annotation that restricts variable ranges for rules
#[derive(Debug)]
pub struct TypeAnnotation<'a> {
    /// [Span] associated with this node
    span: Span<'a>,
    /// Atom to be restricted
    tag: StructureTag<'a>,
    /// [Sequence] containing the type annotations
    body: TypeLiteralSequence<'a>,
}

impl<'a> TypeAnnotation<'a> {
    /// Return the body of the global annotation
    pub fn body(&self) -> impl Iterator<Item = &TypeLiteral<'a>> {
        self.body.iter()
    }

    /// Return the [StructureTag] for the atom that is typed
    pub fn tag(&self) -> &StructureTag<'a>{
        &self.tag
    }
}

const CONTEXT: ParserContext = ParserContext::TypeAnnotation;

impl<'a> ProgramAST<'a> for TypeAnnotation<'a> {
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
                tuple((
                        Token::open_type_annotation, 
                        WSoC::parse, 
                        pair(
                            StructureTag::parse,
                            delimited(
                                pair(Token::atom_open, WSoC::parse),
                                TypeLiteralSequence::parse,
                                pair(WSoC::parse, Token::atom_close),
                            ),
                        ),
                    )),     
        )(input)
        .map(|(rest, (_,_,(tag, body) ),  )| {
            let rest_span = rest.span;

            (
                rest,
                Self {
                    span: input_span.until_rest(&rest_span),
                    tag,
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
        ast::{ProgramAST, type_annotation::TypeAnnotation},
        input::ParserInput,
    };

    #[test]
    fn parse_annotation() {
        let test = vec![
            ("#type test(_,int)", ("test".to_string())),
            ("#type bla(str)", ("bla".to_string())),
        ];

        for (input, expected) in test {
            let parser_input = ParserInput::new(input, ParserState::default());
            let result = all_consuming(TypeAnnotation::parse)(parser_input);

            assert!(result.is_ok());

            let result = result.unwrap();
            println!("");
            assert_eq!(result.1.tag().to_string(), expected);
        }
    }
}
