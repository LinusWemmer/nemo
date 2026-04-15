//! This mod defines [NormalizedRuleAnnotation]

use crate::{execution::planning::normalization::operation::Operation, rule_model::components::term::primitive::variable::Variable};

/// Represents a normalized Rule Annotation
#[derive(Debug, Clone)]
pub struct NormalizedRuleAnnotation{
    /// Restrictions placed on the associated rule
    body: Vec<Operation>,
}

impl NormalizedRuleAnnotation{
    /// Return the list of body operations of the annotation
    pub fn body (&self) -> &Vec<Operation>{
        &self.body
    }

    /// Return the variables restricted in the annotation
    pub fn variables(&self) -> impl Iterator<Item = &Variable>{
        self.body.iter().flat_map(|operation| operation.variables())
    }
}

impl NormalizedRuleAnnotation{

    /// Normalizes a rule annotation
    pub fn normalize_rule_annotation(annotation: &crate::rule_model::components::rule_annotation::RuleAnnotation)
    -> Self
    {
        let body = annotation.body()
            .iter()
            .map(Operation::normalize_body_operation)
            .collect::<Vec<_>>();
        Self {
            body
        }
    }
}