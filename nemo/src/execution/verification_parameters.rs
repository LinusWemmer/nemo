//! This module defines [VerificationParameters].

/// Externally modify the export statements of the program
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub enum ValueAnnotationParameters {
    /// No verification
    #[default]
    None,
    /// Verify without propagation
    NoProp,
    /// Verify with propagation
    Prop,
}

///Cli arguments for verification
#[derive(Debug, Copy, Clone)]
pub struct VerificationParameters {
    ///Check value annotation
    pub annotation_setting: ValueAnnotationParameters,
    ///Check termination
    pub ct: bool,
}

impl Default for VerificationParameters {
    fn default() -> Self {
        Self {
            annotation_setting: ValueAnnotationParameters::None,
            ct: false,
        }
    }
}

impl VerificationParameters {
    /// Create a new [VerificationParameters] object
    pub fn new(ct: bool, annotation_setting: ValueAnnotationParameters) -> Self {
        Self {
            annotation_setting,
            ct,
        }
    }
}
