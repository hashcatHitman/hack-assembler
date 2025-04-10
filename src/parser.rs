//! # Hack Parser
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
//! The parser module is responsible for reading `*.asm` files and parsing them
//! into symbols for assembly.
//!
//! For example, all of the following will be read correctly except "fail",
//! which is not a valid Hack assembly instruction:
//! ```
//! use hack_assembler::parser::{Code, Instruction, ParserError};
//! use std::str::FromStr;
//!
//! let instructions: [&str; 5] =
//!     [" (wow)\n", "@var", "@100", "\tADM=M-1;JNE", "fail"];
//!
//! for instruction in instructions {
//!     let instruction: Result<Instruction, ParserError> =
//!         Instruction::from_str(instruction);
//!     match instruction {
//!         Ok(
//!             instruction @ (Instruction::AddressLiteral(_)
//!             | Instruction::AddressSymbolic(_)),
//!         ) => {
//!             println!(
//!                 "Found address: {} with code {}",
//!                 instruction,
//!                 instruction.code()
//!             );
//!         }
//!         Ok(instruction @ Instruction::Label(_)) => {
//!             println!(
//!                 "Found label: {} with code {}",
//!                 instruction,
//!                 instruction.code()
//!             );
//!         }
//!         Ok(instruction @ Instruction::Compute(..)) => {
//!             println!(
//!                 "Found compute: {} with code {}",
//!                 instruction,
//!                 instruction.code()
//!             );
//!         }
//!         Err(error) => eprintln!("{error}"),
//!     }
//! }
//! ```

mod codegen;
mod error;

use std::convert::TryFrom;
use std::fmt::Display;
use std::fs::read_to_string;
use std::iter::Iterator;
use std::str::FromStr;
use strum::VariantNames;
use strum_macros::{EnumIter, EnumProperty, EnumString, VariantNames};

pub use codegen::Code;
pub use error::ParserError;

/// The [`Destination`] portion of a [`Instruction::Compute`].
///
/// Represents where the value of a C-instruction should be stored. There are 8
/// possibilities, one of which is [`Destination::None`]. In their binary
/// representation, the first bit is whether or not to store in the `A`
/// register, the second bit is whether or not to store in the `D` register,
/// the third bit is whether or not to store in `RAM[A]`.
#[derive(
    Debug,
    Clone,
    Copy,
    Hash,
    strum_macros::Display,
    EnumIter,
    EnumProperty,
    EnumString,
    VariantNames,
)]
pub enum Destination {
    /// Store in: `RAM[A]`.
    #[strum(props(code = "001"), to_string = "M")]
    M,
    /// Store in: `D` register.
    #[strum(props(code = "010"), to_string = "D")]
    D,
    /// Store in: `D` register and `RAM[A]`.
    #[strum(props(code = "011"), to_string = "DM", serialize = "MD")]
    DM,
    /// Store in: `A` register.
    #[strum(props(code = "100"), to_string = "A")]
    A,
    /// Store in: `A` register and `RAM[A]`.
    #[strum(props(code = "101"), to_string = "AM", serialize = "MA")]
    AM,
    /// Store in: `A` register and `D` register.
    #[strum(props(code = "110"), to_string = "AD", serialize = "DA")]
    AD,
    /// Store in: `A` register, `D` register, and `RAM[A]`.
    #[strum(
        props(code = "111"),
        to_string = "ADM",
        serialize = "AMD",
        serialize = "MAD",
        serialize = "MDA",
        serialize = "DMA",
        serialize = "DAM"
    )]
    ADM,
    /// The value is not stored.
    #[strum(props(code = "000"), to_string = "")]
    None,
}

/// The [`Compute`] portion of a [`Instruction::Compute`].
///
/// Represents what a C-instruction should calculate through the ALU. There are
/// 28 possibilities, represented by 7 bits (`a`, `c1`, `c2`, `c3`, `c4`, `c5`,
/// `c6`).
///
/// When the `a` bit is `0`, all operations that do not involve `RAM[A]`
/// can be done. When the `a` bit is `1`, only operations involving `RAM[A]` are
/// defined behavior.
///
/// The remaining bits correspond to the control bits of the ALU when `x` is the
/// `D` register and `y` is `A` or `RAM[A]`, depending on the value of the `a`
/// bit:
/// - `c1` = `zx` = set `x` to `0`
/// - `c2` = `nx` = logical negation of `x`
/// - `c3` = `zy` = set `y` to `0`
/// - `c4` = `ny` = logical negation of `y`
/// - `c5` = `f` = if `1`, do `x + y`, else do `x & y`
/// - `c6` = `no` = if `1`, logical negation of result from `c5`/`f`
#[derive(
    Debug,
    Clone,
    Copy,
    Hash,
    strum_macros::Display,
    EnumIter,
    EnumProperty,
    EnumString,
    VariantNames,
)]
pub enum Compute {
    /// Compute: `0`.
    #[strum(props(code = "0101010"), to_string = "0")]
    Zero,
    /// Compute: `1`.
    #[strum(props(code = "0111111"), to_string = "1")]
    One,
    /// Compute: `-1`.
    #[strum(props(code = "0111010"), to_string = "-1")]
    NegativeOne,
    /// Compute: the value in the `D` register.
    #[strum(props(code = "0001100"), to_string = "D")]
    D,
    /// Compute: the value in the `A` register.
    #[strum(props(code = "0110000"), to_string = "A")]
    A,
    /// Compute: the value in `RAM[A]`.
    #[strum(props(code = "1110000"), to_string = "M")]
    M,
    /// Compute: bitwise negation of the value in the `D` register.
    #[strum(props(code = "0001101"), to_string = "!D")]
    NotD,
    /// Compute: bitwise negation of the value in the `A` register.
    #[strum(props(code = "0110001"), to_string = "!A")]
    NotA,
    /// Compute: bitwise negation of the value in `RAM[A]`.
    #[strum(props(code = "1110001"), to_string = "!M")]
    NotM,
    /// Compute: arithmetic negation of the value in the `D` register.
    #[strum(props(code = "0001111"), to_string = "-D")]
    NegativeD,
    /// Compute: arithmetic negation of the value in the `A` register.
    #[strum(props(code = "0110011"), to_string = "-A")]
    NegativeA,
    /// Compute: arithmetic negation of the value in `RAM[A]`.
    #[strum(props(code = "1110011"), to_string = "-M")]
    NegativeM,
    /// Compute: the value in the `D` register plus `1`.
    #[strum(props(code = "0011111"), to_string = "D+1", serialize = "1+D")]
    DPlusOne,
    /// Compute: the value in the `A` register plus `1`.
    #[strum(props(code = "0110111"), to_string = "A+1", serialize = "1+A")]
    APlusOne,
    /// Compute: the value in `RAM[A]` plus `1`.
    #[strum(props(code = "1110111"), to_string = "M+1", serialize = "1+M")]
    MPlusOne,
    /// Compute: the value in the `D` register minus `1`.
    #[strum(props(code = "0001110"), to_string = "D-1")]
    DMinusOne,
    /// Compute: the value in the `A` register minus `1`.
    #[strum(props(code = "0110010"), to_string = "A-1")]
    AMinusOne,
    /// Compute: the value in `RAM[A]` minus `1`.
    #[strum(props(code = "1110010"), to_string = "M-1")]
    MMinusOne,
    /// Compute: the value in the `D` register plus the value in the `A`
    /// register.
    #[strum(props(code = "0000010"), to_string = "D+A", serialize = "A+D")]
    DPlusA,
    /// Compute: the value in the `D` register plus the value in `RAM[A]`.
    #[strum(props(code = "1000010"), to_string = "D+M", serialize = "M+D")]
    DPlusM,
    /// Compute: the value in the `D` register minus the value in the `A`
    /// register.
    #[strum(props(code = "0010011"), to_string = "D-A")]
    DMinusA,
    /// Compute: the value in the `D` register minus the value in `RAM[A]`.
    #[strum(props(code = "1010011"), to_string = "D-M")]
    DMinusM,
    /// Compute: the value in the `A` register minus the value in the `D`
    /// register.
    #[strum(props(code = "0000111"), to_string = "A-D")]
    AMinusD,
    /// Compute: the value in `RAM[A]` minus the value in the `D` register.
    #[strum(props(code = "1000111"), to_string = "M-D")]
    MMinusD,
    /// Compute: the bitwise AND of the value in the `D` register and the value
    /// in the `A` register.
    #[strum(props(code = "0000000"), to_string = "D&A", serialize = "A&D")]
    DAndA,
    /// Compute: the bitwise AND of the value in the `D` register and the value
    /// in `RAM[A]`.
    #[strum(props(code = "1000000"), to_string = "D&M", serialize = "M&D")]
    DAndM,
    /// Compute: the bitwise OR of the value in the `D` register and the value
    /// in the `A` register.
    #[strum(props(code = "0010101"), to_string = "D|A", serialize = "A|D")]
    DOrA,
    /// Compute: the bitwise OR of the value in the `D` register and the value
    /// in `RAM[A]`.
    #[strum(props(code = "1010101"), to_string = "D|M", serialize = "M|D")]
    DOrM,
}

/// The [`Jump`] portion of a [`Instruction::Compute`].
///
/// Represents the condition under which a C-instruction should jump, as a
/// comparison between the [`Compute`] portion and `0`. There are 8
/// possibilities, one of which is [`Jump::None`]. In their binary
/// representation, the first bit is whether or not to jump if [`Compute`] is
/// less than `0`, the second bit is whether or not to jump if [`Compute`] is
/// equal to `0`, and the third bit is whether or not to jump if [`Compute`] is
/// greater than `0`.
#[derive(
    Debug,
    Clone,
    Copy,
    Hash,
    strum_macros::Display,
    EnumIter,
    EnumProperty,
    EnumString,
    VariantNames,
)]
#[strum(serialize_all = "UPPERCASE")]
pub enum Jump {
    /// Jump if: [`Compute`] > `0`.
    #[strum(props(code = "001"))]
    JGT,
    /// Jump if: [`Compute`] == `0`.
    #[strum(props(code = "010"))]
    JEQ,
    /// Jump if: [`Compute`] >= `0`.
    #[strum(props(code = "011"))]
    JGE,
    /// Jump if: [`Compute`] < `0`.
    #[strum(props(code = "100"))]
    JLT,
    /// Jump if: [`Compute`] != `0`.
    #[strum(props(code = "101"))]
    JNE,
    /// Jump if: [`Compute`] <= `0`.
    #[strum(props(code = "110"))]
    JLE,
    /// Jump.
    #[strum(props(code = "111"))]
    JMP,
    /// Don't jump.
    #[strum(props(code = "000"), to_string = "")]
    None,
}

/// The [`Parser`] is used to read the contents of a [`std::fs::File`] line by
/// line, parsing the text into instructions that can be assembled into binary.
///
/// To create and use a new parser:
/// ```
/// use hack_assembler::parser::{Parser, ParserError};
///
/// // Tries to read the contents of `foo.asm`.
/// let parser: Result<Parser, ParserError> = Parser::try_from("foo.asm");
/// match parser {
///     Ok(parser) => {
///         // Prints every line of `foo.asm`
///         parser.lines().for_each(|line: &str| println!("{line}"));
///         // Does it again, from the start.
///         parser.lines().for_each(|line: &str| println!("{line}"));
///         }
///     Err(_) => println!("Failure!"),
/// }
/// ```
#[derive(Debug, Clone, Hash)]
pub struct Parser {
    /// The contents of the file as a String.
    file: String,
}

impl Parser {
    /// Returns an [`Iterator`] over the lines of a the held file contents, as
    /// string slices.
    pub fn lines(&self) -> impl Iterator<Item = &str> {
        self.file.lines().filter(|line| !line.starts_with("//"))
    }
}

impl TryFrom<&str> for Parser {
    type Error = ParserError;

    /// Tries to read the contents of a file located at the path indicated by
    /// `value`.
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let file: String = read_to_string(value)?;
        Ok(Self { file })
    }
}

/// The two types of [`Instruction`] (and the one pseudo-instruction) supported
/// by the Hack CPU.
#[derive(Debug, Clone, Hash)]
pub enum Instruction {
    /// [`Instruction::AddressSymbolic`] represents an A-instruction. The
    /// [`String`] inside should be the symbol that would come after the `@`.
    ///
    /// Example:
    /// ```
    /// use hack_assembler::parser::Instruction;
    ///
    /// // @my_var
    /// Instruction::AddressSymbolic("my_var".into());
    /// ```
    AddressSymbolic(String),
    /// [`Instruction::AddressLiteral`] represents an A-instruction. The
    /// [`u16`] inside should be the numerical constant that would come after
    /// the `@`. It must be less than or equal to
    /// [`Instruction::MAX_VALID_CONSTANT`].
    ///
    /// Examples:
    /// ```
    /// use hack_assembler::parser::Instruction;
    ///
    /// // @1984
    /// Instruction::AddressLiteral(1984);
    /// ```
    AddressLiteral(u16),
    /// [`Instruction::Compute`] represents a C-instruction. It is already
    /// broken into the three parts, which have their own types.
    ///
    /// See [`Destination`], [`Compute`], and [`Jump`] for detailed information.
    Compute(Destination, Compute, Jump),
    /// [`Instruction::Label`] represents the label pseudo-instruction. The
    /// [`String`] inside should be the symbol that would go inside the
    /// parentheses.
    ///
    /// Example:
    /// ```
    /// use hack_assembler::parser::Instruction;
    ///
    /// // (LOOP)
    /// Instruction::Label("LOOP".into());
    /// ```
    Label(String),
}

impl Instruction {
    /// The highest valid constant in the Hack computer.
    pub const MAX_VALID_CONSTANT: u16 = 0x7FFF;

    /// Attempts to parse a [`Instruction::Label`] from a string.
    fn try_parse_label(label: &str) -> Result<Self, ParserError> {
        if !(label.starts_with('(') && label.ends_with(')')) {
            return Err(ParserError::LabelHasBadParentheses);
        }
        let symbol: &str = &label[1..label.len() - 1];
        match symbol {
            symbol if symbol.contains(['(', ')']) => {
                Err(ParserError::LabelHasBadParentheses)
            }
            symbol if !Self::is_allowed_symbol(symbol) => {
                Err(ParserError::SymbolHasForbiddenCharacter)
            }
            _ => Ok(Self::Label(label[1..label.len() - 1].into())),
        }
    }

    /// Attempts to parse an [`Instruction::AddressLiteral`] or an
    /// [`Instruction::AddressSymbolic`] from a string.
    fn try_parse_address(address: &str) -> Result<Self, ParserError> {
        let address: &str = &address[1..];
        let parsed: Result<u16, _> = address.parse();
        match (address, parsed) {
            (address, Ok(parsed))
                if Self::is_allowed_constant(address, parsed) =>
            {
                Ok(Self::AddressLiteral(parsed))
            }
            (symbol, _) if Self::is_allowed_symbol(symbol) => {
                Ok(Self::AddressSymbolic(symbol.into()))
            }
            _ => Err(ParserError::InvalidAddress),
        }
    }

    /// Attempts to parse a [`Instruction::Compute`] from a string.
    fn try_parse_compute(compute: &str) -> Result<Self, ParserError> {
        let split: [&str; 3] = Self::decompose_compute_instruction(compute);
        let mut compare: String = String::new();
        if !split[0].is_empty() {
            compare.push_str(split[0]);
            compare.push('=');
        }
        compare.push_str(split[1]);
        if !split[2].is_empty() {
            compare.push(';');
            compare.push_str(split[2]);
        }
        if Compute::VARIANTS.contains(&split[1]) && compare == compute {
            return Ok(Self::Compute(
                Destination::from_str(split[0])
                    .map_err(|_| ParserError::UnrecognizedInstruction)?,
                Compute::from_str(split[1])
                    .map_err(|_| ParserError::UnrecognizedInstruction)?,
                Jump::from_str(split[2])
                    .map_err(|_| ParserError::UnrecognizedInstruction)?,
            ));
        }
        Err(ParserError::UnrecognizedInstruction)
    }

    /// Takes a reference to a string and attempts to split it into the parts
    /// of a [`Instruction::Compute`].
    fn decompose_compute_instruction(string: &str) -> [&str; 3] {
        let separators: [char; 2] = ['=', ';'];
        let mut parts: Vec<&str> = string.split(separators).collect();
        let mut dest: &str = "";
        let mut jump: &str = "";
        let comp: &str;
        match string {
            string
                if string.contains(separators[0])
                    && string.contains(separators[1])
                    && parts.len() == 3 =>
            {
                dest = parts.remove(0);
                comp = parts.remove(0);
                jump = parts.remove(0);
            }
            string if string.contains(separators[0]) && parts.len() == 2 => {
                dest = parts.remove(0);
                comp = parts.remove(0);
            }
            string if string.contains(separators[1]) && parts.len() == 2 => {
                comp = parts.remove(0);
                jump = parts.remove(0);
            }
            string => comp = string,
        }
        [dest, comp, jump]
    }

    /// Determine if a given string is a valid symbol.
    ///
    /// A symbol must be a sequence of letters (a-z || A-Z), digits (0-9),
    /// underscores (_), dots (.), dollar signs ($), and/or colons (:) that does
    /// not begin with a digit.
    fn is_allowed_symbol(string: &str) -> bool {
        !string.is_empty()
            && !string.contains(|character: char| {
                !(character.is_ascii_alphanumeric()
                    || character == '_'
                    || character == ':'
                    || character == '.'
                    || character == '$')
            })
            && !string
                .starts_with(|character: char| char::is_ascii_digit(&character))
    }

    /// Determine if a given string is a valid constant.
    ///
    /// Constants must be non-negative and are always written in decimal
    /// notation. They should not exceed [`Self::MAX_VALID_CONSTANT`].
    fn is_allowed_constant(string: &str, value: u16) -> bool {
        !string.is_empty()
            && !string.contains(|character: char| !(character.is_ascii_digit()))
            && value <= Self::MAX_VALID_CONSTANT
    }
}

impl FromStr for Instruction {
    type Err = ParserError;

    /// Attempts to parse a string into a valid [`Instruction`].
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.trim() {
            label if label.starts_with('(') || label.ends_with(')') => {
                Self::try_parse_label(label)
            }
            address if address.starts_with('@') => {
                Self::try_parse_address(address)
            }
            compute => Self::try_parse_compute(compute),
        }
    }
}

impl Display for Instruction {
    /// Attempts to create a string representation of this [`Instruction`].
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AddressLiteral(address) => {
                write!(f, "{address}")
            }
            Self::AddressSymbolic(address) => {
                write!(f, "{address}")
            }
            Self::Compute(dest, comp, jump) => {
                let mut compute: String = String::new();

                if !matches!(dest, Destination::None) {
                    compute.push_str(&dest.to_string());
                    compute.push('=');
                }

                compute.push_str(&comp.to_string());

                if !matches!(jump, Jump::None) {
                    compute.push(';');
                    compute.push_str(&jump.to_string());
                }

                write!(f, "{compute}")
            }
            Self::Label(label) => write!(f, "{label}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allowed_symbols() {
        let symbols: [&str; 4] = ["LOOP", "$1.99:dollar_amount", "i", "R0"];
        for symbol in &symbols {
            assert!(Instruction::is_allowed_symbol(symbol));
        }
    }

    #[test]
    fn disallowed_symbols() {
        let symbols: [&str; 4] = ["", "3cats", "my symbol", "@everyone"];
        for symbol in &symbols {
            assert!(!Instruction::is_allowed_symbol(symbol));
        }
    }

    #[test]
    fn memory_address_safety() {
        let less: String = format!("{}", Instruction::MAX_VALID_CONSTANT - 1);
        let max: String = format!("{}", Instruction::MAX_VALID_CONSTANT);
        let more: String = format!("{}", Instruction::MAX_VALID_CONSTANT + 1);
        assert!(less < max);
        assert!(less < more);
        assert!(max > less);
        assert!(max < more);
        assert!(more > less);
        assert!(more > max);

        if let (Ok(little), Ok(maxed), Ok(over)) =
            (less.parse(), max.parse(), more.parse())
        {
            assert!(Instruction::is_allowed_constant(&less, little));
            assert!(Instruction::is_allowed_constant(&max, maxed));
            assert!(!Instruction::is_allowed_constant(&more, over));
        }
    }

    #[test]
    fn read_address() {
        let instructions: [&str; 4] = ["@200", "@variable", "@LOOP", "@R16"];
        for instruction in instructions {
            match Instruction::from_str(instruction) {
                Ok(
                    Instruction::AddressSymbolic(_)
                    | Instruction::AddressLiteral(_),
                ) => (),
                _ => panic!("failed to correctly parse a good address"),
            }
        }

        let bad_instructions: [&str; 4] = ["@@200", "@var*iable", "", "(@R16"];
        for instruction in bad_instructions {
            assert!(Instruction::from_str(instruction).is_err());
        }
    }

    #[test]
    fn read_label() {
        let instructions: [&str; 4] = ["(START)", "(_)", "($1.99)", "(neat.)"];
        for instruction in instructions {
            assert!(matches!(
                Instruction::from_str(instruction),
                Ok(Instruction::Label(_))
            ));
        }

        let bad_instructions: [&str; 4] = ["(START", "()", "", "(16R)"];
        for instruction in bad_instructions {
            assert!(Instruction::from_str(instruction).is_err());
        }
    }

    #[test]
    fn read_compute() {
        let instructions: [&str; 5] =
            ["DM=1;JMP", "MD=M-1;JLE", "D", "ADM=0", "0;JLE"];
        for instruction in instructions {
            assert!(matches!(
                Instruction::from_str(instruction),
                Ok(Instruction::Compute(..))
            ));
        }

        let bad_instructions: [&str; 4] = ["E=1", "45", "", "=;"];
        for instruction in bad_instructions {
            assert!(Instruction::from_str(instruction).is_err());
        }
    }
}
