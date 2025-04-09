//! # Parser Errors
//!
//! <details>
//!     <summary>Licensing Info</summary>
//!
//! > hack-assembler - An assembler that translates programs written in the Hack
//! > assembly language into Hack binary code.
//! > Copyright (C) 2025  [hashcatHitman] and [jlg-repo]
//! >
//! > This program is free software: you can redistribute it and/or modify
//! > it under the terms of the GNU Affero General Public License as published
//! > by the Free Software Foundation, either version 3 of the License, or
//! > (at your option) any later version.
//! >
//! > This program is distributed in the hope that it will be useful,
//! > but WITHOUT ANY WARRANTY; without even the implied warranty of
//! > MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//! > GNU Affero General Public License for more details.
//! >
//! > You should have received a copy of the GNU Affero General Public License
//! > along with this program.  If not, see <https://www.gnu.org/licenses/>.
//!
//! [hashcatHitman]: https://github.com/hashcatHitman
//! [jlg-repo]: https://github.com/jlg-repo
//!
//! </details>
//!
//! A submodule containing the various [`ParserError`]s that can occur.

use std::fmt::Display;
use std::io::Error;

use super::Instruction;

/// An enum containing all [`ParserError`]s.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
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
                    Instruction::MAX_VALID_CONSTANT
                );
            }
        };

        write!(f, "{message}")
    }
}
