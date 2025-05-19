// SPDX-FileCopyrightText: Copyright © 2025 hashcatHitman
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # Hack Assembler
//!
//! `hack-assembler` is a crate providing an assembler that translates programs
//! written in the Hack assembly language into Hack binary code. Based on the
//! nand2tetris course.

use std::io::Write;
use std::path::Path;

use self::error::HackError;
use self::parser::{Code, Instruction, Parser};
use self::symbol_table::{SymbolTable, SymbolError};

pub mod error;
pub mod parser;

pub mod symbol_table;

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
    pub fn build(
        mut args: impl Iterator<Item = String>,
    ) -> Result<Self, HackError> {
        let _ = args.next();

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
    let mut symbol_table = symbol_table::SymbolTable::new();

    // First pass: Build symbol table (labels only)
    let mut rom_address = 0;
    for line in parser.lines() {
        match Instruction::try_from(line) {
            Ok(Instruction::Label(symbol)) => {
                symbol_table.add_label(&symbol, rom_address)?;

            }
            Ok(Instruction::AddressLiteral(_) |
            Instruction::AddressSymbolic(_) |
            Instruction::Compute(..)) => {
                rom_address += 1;
            }
            Err(error) => return Err(error),
        }
    }
    //Second pass: Generate code
    let codes = parser
        .lines()
        .map(|line: &str| Instruction::try_from(line))
        .filter_map(|instruction_result| -> Option<Result<String, HackError>> {
            match instruction_result {
                Ok(Instruction::AddressSymbolic(symbol)) => {
                    let address = symbol_table.get_or_add_variable(&symbol);
                    let binary = format!("0{:015b}", address);
                    println!("@{} which formats to {}", symbol, binary);
                    Some(Ok(binary))
                }
                Ok(Instruction::AddressLiteral(address)) => {
                    let binary = format!("0{:015b}", address);
                    println!("@{} which formats to {}", address, binary);
                    Some(Ok(binary))
                }
                Ok(
                    instruction @ Instruction::Compute(..)) => {
                        println!(
                        "{instruction} which formats to {}",
                        instruction.code()
                        );
                Some(Ok(instruction.code()))
                }
                Ok(Instruction::Label(_)) => {
                    None //labels don't generate code
                }
                Err(error) => Some(Err(error)),
            }
        })
                .map(|result| {
                     result.map(|mut instruction| {
                                instruction.push('\n');
                                instruction
                                })
                     });
    let new_file: String = match config.file_path().strip_suffix(".asm") {
        Some(filename) => [filename, ".hack"].concat(),
        None => return Err(HackError::BadFileTypeError),
    };

    let file: std::fs::File = match std::path::Path::new(&new_file).exists() {
        true => return Err(HackError::FileExistsError { certain: true }),
        false => std::fs::File::create(new_file)?,

    };

    let codes: Result<Vec<String>, HackError> = codes.collect();

    let codes: String = match codes {
        Ok(codes) => codes.concat(),
        Err(error) => return Err(error),
    };

    let mut file: std::fs::File = file;
    println!("{codes}");
    let result: Result<(), std::io::Error> = file.write_all(codes.as_bytes());
    let file: std::fs::File = file;
    file.set_modified(std::time::SystemTime::now())?;

    result.map_err(|error: std::io::Error| {
        HackError::WriteError(error.to_string())
    })
}
