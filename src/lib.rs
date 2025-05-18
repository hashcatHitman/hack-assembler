// SPDX-FileCopyrightText: Copyright © 2025 hashcatHitman
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # Hack Assembler
//!
//! `hack-assembler` is a crate providing an assembler that translates programs
//! written in the Hack assembly language into Hack binary code. Based on the
//! nand2tetris course.

#![feature(
    strict_provenance_lints,
    unqualified_local_imports,
    must_not_suspend,
    iterator_try_collect
)]

use std::io::Write as _;
use std::time::SystemTime;
use std::{fs, io};

use self::error::HackError;
use self::parser::{Code as _, Instruction, Parser};

pub mod error;
pub mod parser;

/// The basic configuration of the binary, storing the results from a successful
/// command-line invocation.
#[derive(Debug, Clone, Hash)]
pub struct Config {
    /// The path to the target Hack `.asm` file, as a String.
    file_path: String,
}

impl Config {
    /// Attempts to build a valid [`Config`] from the arguments passed on the
    /// command line.
    ///
    /// A valid [`Config`] consists of just a single argument passed - the path
    /// to a Hack ASM file.
    ///
    /// Example:
    /// ```bash
    /// hack-assembler ./foo.asm
    /// ```
    /// # Errors
    ///
    /// There are two conditions under which this will return an error:
    ///
    /// - No arguments were passed.
    ///
    /// - More than one argument was passed.
    ///
    /// In either scenario, the error received will be a
    /// [`HackError::Misconfiguration`] holding the number of arguments that
    /// were passed, up to a limit of [`usize::MAX`].
    pub fn build<I: Iterator<Item = String>>(
        mut args: I,
    ) -> Result<Self, HackError> {
        let _skip_first = args.next();

        let file_path: String = match args.next() {
            Some(file_path) => file_path,
            None => return Err(HackError::Misconfiguration(0)),
        };

        if args.next().is_some() {
            if let Some(count) = args.count().checked_add(2) {
                return Err(HackError::Misconfiguration(count));
            }
            return Err(HackError::Misconfiguration(usize::MAX));
        }

        Ok(Self { file_path })
    }

    /// Gets a shared reference to [`Config::file_path`].
    ///
    /// This is the path to the target Hack `.asm` file, as a borrowed [str].
    pub fn file_path(&self) -> &str {
        &self.file_path
    }
}

/// Given a borrow of a valid [`Config`], runs the main program logic.
///
/// If the [`Config`] is targeting a valid Hack assembly file, it will be read
/// into memory and have each line deserialized into an [`Instruction`].
///
/// On the first pass, [`Instruction::AddressSymbolic`]s and
/// [`Instruction::Label`]s will be added to the symbol table.
///
/// On the second pass, all [`Instruction`]s are compiled into their Hack binary
/// represenation.
///
/// If the input file was `foo.asm`, the program will try to write the output to
/// `foo.hack`. However, it will only do this if `foo.hack` absolutely does not
/// already exist. If there is ambiguity, or the file exists, it will not be
/// overwritten.
///
/// # Errors
///
/// Any non-[`Config`] error that can happen is eventually propagated here. See
/// the [`crate::error`] module for more details.
pub fn run(config: &Config) -> Result<(), HackError> {
    let parser: Parser = Parser::try_from(config.file_path())?;

    let codes = parser
        .lines()
        .map(|line: &str| Instruction::try_from(line))
        .map(|instruction: Result<Instruction, HackError>| {
            Ok(match instruction {
                Ok(
                    instruction @ (Instruction::Compute(..)
                    | Instruction::AddressLiteral(..)),
                ) => instruction,
                Ok(_instruction) => todo!("TODO: Needs symbol table."),
                Err(error) => return Err(error),
            })
        })
        .map(|instruction: Result<Instruction, HackError>| {
            Ok(match instruction {
                Ok(instruction) => {
                    println!(
                        "{instruction} which formats to {}",
                        instruction.code()?
                    );
                    instruction.code()?
                }
                Err(error) => return Err(error),
            })
        });
    let new_file: String = match config.file_path().strip_suffix(".asm") {
        Some(filename) => [filename, ".hack"].concat(),
        None => return Err(HackError::BadFileTypeError),
    };

    let file: fs::File = match fs::exists(&new_file) {
        Ok(true) => return Err(HackError::FileExistsError { certain: true }),
        Ok(false) => fs::File::create(new_file)?,
        Err(_) => return Err(HackError::FileExistsError { certain: false }),
    };

    let codes: Result<Vec<String>, HackError> = codes
        .map(|instruction: Result<String, HackError>| match instruction {
            Ok(mut instruction) => {
                instruction.push('\n');
                Ok(instruction)
            }
            Err(error) => Err(error),
        })
        .collect();

    let codes: String = match codes {
        Ok(codes) => codes.concat(),
        Err(error) => return Err(error),
    };

    let mut file: fs::File = file;
    println!("{codes}");
    let result: Result<(), io::Error> = file.write_all(codes.as_bytes());
    let file: fs::File = file;
    file.set_modified(SystemTime::now())?;

    result.map_err(|error: io::Error| HackError::WriteError(error.to_string()))
}
