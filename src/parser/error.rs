//! # Parser Errors
//!
//! A submodule containing the various [`ParserError`]s that can occur.

use std::fmt::Display;
use std::io::Error;

use super::Instruction;

/// An enum containing all [`ParserError`]s.
#[derive(Debug, PartialEq, Eq)]
pub enum ParserError {
    /// A [`ParserError`] returned when failing to read the file provided.
    CannotReadFileFromPath(String),
    /// A [`ParserError`] returned when an instruction is suspected to be a
    /// label but does not have the correct number/placement of parentheses.
    LabelHasBadParentheses,
    /// A [`ParserError`] returned when a label or address uses characters not
    /// permitted in valid symbols.
    SymbolHasForbiddenCharacter,
    /// A [`ParserError`] returned whenever we get an instruction we honestly
    /// aren't sure what to do with.
    UnrecognizedInstruction,
    /// A [`ParserError`] returned when an instruction is suspected to be an
    /// address but does not qualify as a valid address of either form.
    InvalidAddress,
}

impl From<Error> for ParserError {
    /// Creates a [`ParserError::CannotReadFileFromPath`] from the [`Error`]
    /// returned by failed file operations.
    fn from(value: Error) -> Self {
        Self::CannotReadFileFromPath(value.to_string())
    }
}

impl Display for ParserError {
    /// Determines the error message for displaying [`ParserError`]s.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message: &str = match self {
            Self::CannotReadFileFromPath(error_message) => error_message,
            Self::LabelHasBadParentheses => {
                "label instructions should be surrounded by exactly one pair \
                of paretheses and contain no others"
            }
            Self::SymbolHasForbiddenCharacter => {
                "symbols must be a sequence of letters (a-z || A-Z), digits \
                (0-9), underscores (_), dots (.), dollar signs ($), and/or \
                colons (:) that does not begin with a digit"
            }
            Self::UnrecognizedInstruction => {
                "could not determine instruction type"
            }
            Self::InvalidAddress => {
                return write!(
                    f,
                    "addresses must be valid symbols or non-negative integers \
                    which are less than or equal to {}",
                    Instruction::MAX_VALID_MEMORY_ADDRESS
                );
            }
        };

        write!(f, "{message}")
    }
}
