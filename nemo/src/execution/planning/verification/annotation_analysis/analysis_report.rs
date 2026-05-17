//! Module defines report of static analysis

use std::fmt::Display;

/// Describes the type of error occuring during type analysis
#[derive(Debug, Copy, Clone)]
pub enum AnalysisErrorKind {
    GlobalAssertFactMismatch,
    NonMatchGlobalAssert,
    NonMatchRuleAssert
}

#[derive(Debug)]
pub struct AnalysisError{
    
    kind: AnalysisErrorKind,

    text: str,

}

impl Display for AnalysisError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {

        match self.kind{
            AnalysisErrorKind::NonMatchGlobalAssert => todo!(),
            AnalysisErrorKind::NonMatchRuleAssert => todo!(),
            AnalysisErrorKind::GlobalAssertFactMismatch => write!(f, "foo")?,
        };
        Ok(())
    }
}