use std::collections::HashMap;

use crate::{
    execution::planning::{
        normalization::{
            operation::Operation,
            rule::{self, NormalizedRule},
        },
        verification::type_verification::relation_types::RelationTypes,
    },
    rule_model::components::{tag::Tag, term::operation::operation_kind::OperationKind},
};
pub mod relation_types;

/// Specifies how storage values are propagated by a function.
pub(crate) enum FunctionTypePropagation {
    /// Possible outputs are knonw in advance
    KnownOutput(StorageTypeBitSet), //TODO
    /// Types are preserved, i.e. the output has the same types as the inputs
    /// (the function returns `None` if input values differ in type)
    Preserve,
    /// If input types are numeric, cast them to the maximum type
    NumericUpcast,
    /// Nothing is known about the the type propagation
    _Unknown,
}

/// Struct that verifies correct typing of a program
#[derive(Debug, Clone)]
pub struct TypeVerifier {
    types: HashMap<Tag, RelationTypes>,
}

impl TypeVerifier {
    /// Creates a new [TypeVerifier]
    pub fn new() -> Self {
        Self {
            types: HashMap::new(),
        }
    }
}

impl TypeVerifier {
    /// Returns the corresponding physical nemo operation for the normalized operation
    /// This is important to get the type propagation kind. This essentially just copies the implementation
    /// The nemo physical implementation
    pub fn get_operation_type_propagation_kind(op_kind: &OperationKind) -> FunctionTypePropagation {
        match op_kind {
            OperationKind::Equal => FunctionTypePropagation::KnownOutput(()),
            OperationKind::Unequals => FunctionTypePropagation::KnownOutput(()),
            OperationKind::NumericSum => FunctionTypePropagation::NumericUpcast,
            OperationKind::NumericSubtraction => FunctionTypePropagation::NumericUpcast,
            OperationKind::NumericProduct => FunctionTypePropagation::NumericUpcast,
            OperationKind::NumericDivision => FunctionTypePropagation::NumericUpcast,
            OperationKind::NumericLogarithm => FunctionTypePropagation::NumericUpcast,
            OperationKind::NumericPower => FunctionTypePropagation::NumericUpcast,
            OperationKind::NumericRemainder => FunctionTypePropagation::NumericUpcast,
            OperationKind::NumericGreaterthaneq => FunctionTypePropagation::KnownOutput(()),
            OperationKind::NumericGreaterthan => FunctionTypePropagation::KnownOutput(()),
            OperationKind::NumericLessthaneq => FunctionTypePropagation::KnownOutput(()),
            OperationKind::NumericLessthan => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringCompare => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringContains => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringRegex => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringSubstring => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringBefore => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringAfter => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringStarts => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringEnds => FunctionTypePropagation::KnownOutput(()),
            OperationKind::StringLevenshtein => FunctionTypePropagation::KnownOutput(()),
            OperationKind::BooleanNegation => todo!(),
            OperationKind::CastToDouble => todo!(),
            OperationKind::CastToFloat => todo!(),
            OperationKind::CastToInteger => todo!(),
            OperationKind::CastToIRI => todo!(),
            OperationKind::CanonicalString => todo!(),
            OperationKind::CheckIsInteger => todo!(),
            OperationKind::CheckIsFloat => todo!(),
            OperationKind::CheckIsDouble => todo!(),
            OperationKind::CheckIsIri => todo!(),
            OperationKind::CheckIsNumeric => todo!(),
            OperationKind::CheckIsNull => todo!(),
            OperationKind::CheckIsString => todo!(),
            OperationKind::Datatype => todo!(),
            OperationKind::LanguageString => todo!(),
            OperationKind::LanguageTag => todo!(),
            OperationKind::NumericAbsolute => todo!(),
            OperationKind::NumericCosine => todo!(),
            OperationKind::NumericCeil => todo!(),
            OperationKind::NumericFloor => todo!(),
            OperationKind::NumericNegation => todo!(),
            OperationKind::NumericRound => todo!(),
            OperationKind::NumericSine => todo!(),
            OperationKind::NumericSquareroot => todo!(),
            OperationKind::NumericTangent => todo!(),
            OperationKind::StringLength => todo!(),
            OperationKind::StringReverse => todo!(),
            OperationKind::StringLowercase => todo!(),
            OperationKind::StringUppercase => todo!(),
            OperationKind::StringUriEncode => todo!(),
            OperationKind::StringUriDecode => todo!(),
            OperationKind::BitAnd => todo!(),
            OperationKind::BitOr => todo!(),
            OperationKind::BitXor => todo!(),
            OperationKind::BitShl => todo!(),
            OperationKind::BitShru => todo!(),
            OperationKind::BitShr => todo!(),
            OperationKind::BooleanConjunction => todo!(),
            OperationKind::BooleanDisjunction => todo!(),
            OperationKind::NumericMinimum => todo!(),
            OperationKind::NumericMaximum => todo!(),
            OperationKind::NumericLukasiewicz => todo!(),
            OperationKind::StringConcatenation => todo!(),
            OperationKind::LexicalValue => todo!(),
        }
    }

    /// Checks if the types are valid & propagates them
    pub fn type_check_rule(&self, rule: NormalizedRule) -> bool {
        true
    }
}
