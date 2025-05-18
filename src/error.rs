// SPDX-FileCopyrightText: Copyright © 2025 hashcatHitman
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # Hack Errors
//!
//! A submodule containing the various [`HackError`]s that can occur.

use core::fmt::{self, Display};
use std::io::Error;

use strum::ParseError;

use crate::parser::Instruction;

/// An enum containing all [`HackError`]s.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[expect(
    clippy::module_name_repetitions,
    reason = "Need to restructure for that. Later."
)]
pub enum HackError {
    /// A [`HackError`] returned when failing to read the file provided. The
    /// [`String`] within is meant to hold some arbitrary, message: typically,
    /// this will be the string representation of the original error,
    /// potentially with added context.
    CannotReadFileFromPath(String),
    /// A [`HackError`] returned when an instruction is suspected to be a
    /// label but does not have the correct number/placement of parentheses.
    LabelHasBadParentheses,
    /// A [`HackError`] returned when a label or address uses characters not
    /// permitted in valid symbols. Symbols must be a sequences of letters
    /// (a-z || A-Z), digits (0-9), underscores (_), dots (.), dollar signs ($),
    /// and/or colons (:) that do not begin with a digit.
    SymbolHasForbiddenCharacter,
    /// A [`HackError`] returned whenever we get an instruction we honestly
    /// aren't sure what to do with, which is contained in its [`String`].
    UnrecognizedInstruction(String, Option<ParseError>),
    /// A [`HackError`] returned when an instruction is suspected to be an
    /// address but does not qualify as a valid address of either form.
    InvalidAddress,
    /// A [`HackError`] returned if the number of arguments received was
    /// unexpected. Contains the number of arguments received as a [`usize`], up
    /// to [`usize::MAX`]. Anything above will simply be represented as
    /// [`usize::MAX`].
    Misconfiguration(usize),
    /// A [`HackError`] returned if we aren't able to write to the output file,
    /// either because it doesn't exist or something else.
    FileExistsError {
        /// True if we're certain it does not exist.
        certain: bool,
    },
    /// A [`HackError`] returned if the target Hack ASM file doesn't end in the
    /// extension `.asm`.
    BadFileTypeError,
    /// A [`HackError`] returned if any errors are thrown when trying to write
    /// the output. The [`String`] within is meant to hold some arbitrary,
    /// message: typically, this will be the string representation of the
    /// original error, potentially with added context.
    WriteError(String),
}

impl From<Error> for HackError {
    /// Creates a [`HackError::CannotReadFileFromPath`] from the [`Error`]
    /// returned by failed file reading operations.
    fn from(value: Error) -> Self {
        Self::CannotReadFileFromPath(value.to_string())
    }
}

impl Display for HackError {
    #[expect(
        clippy::min_ident_chars,
        reason = "https://github.com/rust-lang/rust-clippy/issues/13396"
    )]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let message: &str = match *self {
            Self::LabelHasBadParentheses => {
                "label instructions should be surrounded by exactly one pair \
                of paretheses and contain no others"
            }
            Self::SymbolHasForbiddenCharacter => {
                "symbols must be a sequence of letters (a-z || A-Z), digits \
                (0-9), underscores (_), dots (.), dollar signs ($), and/or \
                colons (:) that does not begin with a digit"
            }
            Self::UnrecognizedInstruction(ref bad_instruction, error) => {
                if let Some(error) = error {
                    return write!(
                        f,
                        "could not determine instruction type for \
                        \"{bad_instruction}\" due to: \"{error}\""
                    );
                }
                return write!(
                    f,
                    "could not determine instruction type for \
                    \"{bad_instruction}\""
                );
            }
            Self::InvalidAddress => {
                return write!(
                    f,
                    "addresses must be valid symbols or non-negative integers \
                    which are less than or equal to {}",
                    Instruction::MAX_VALID_CONSTANT
                );
            }
            Self::Misconfiguration(args) => {
                return write!(
                    f,
                    "expected 1 argument (file.asm), found {args} arguments",
                );
            }
            Self::FileExistsError { certain } => {
                if certain {
                    "the target output file already exists, and this program \
                    refuses to overwrite it"
                } else {
                    "there is uncertainty about whether or not it is safe to \
                    create a new file of the target name"
                }
            }
            Self::BadFileTypeError => {
                "the target file must have the \".asm\" extension"
            }
            Self::WriteError(ref error_message)
            | Self::CannotReadFileFromPath(ref error_message) => error_message,
        };

        write!(f, "{message}")
    }
}
