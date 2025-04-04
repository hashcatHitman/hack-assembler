//! # Hack Parser
//!
//! The parser module is responsible for reading `*.asm` files and parsing them
//! into symbols for assembly.
//!
//! For example, all of the following will be read correctly except "fail",
//! which is not a valid Hack assembly instruction:
//! ```
//! use std::str::FromStr;
//! use hack_assembler::parser::Instruction;
//! use hack_assembler::parser::ParserError;
//!
//! let instructions: [&str; 5] =
//!     [" (wow)\n", "@var", "@100", "\tADM=M-1;JNE", "fail"];
//!
//! for instruction in instructions {
//!     let instruction: Result<Instruction, ParserError> =
//!         Instruction::from_str(instruction);
//!     match instruction {
//!         Ok(Instruction::Address(instruction)) => {
//!             println!(
//!                 "Found address: {}",
//!                 Instruction::Address(instruction)
//!             );
//!         }
//!         Ok(Instruction::Label(instruction)) => {
//!             println!("Found label: {}", Instruction::Label(instruction));
//!         }
//!         Ok(Instruction::Compute(d, c, j)) => {
//!             println!("Found compute: {}", Instruction::Compute(d, c, j));
//!         }
//!         Err(error) => eprintln!("{error}"),
//!     }
//! }
//! ```

use std::convert::TryFrom;
use std::fmt::Display;
use std::fs::read_to_string;
use std::iter::Iterator;
use std::str::FromStr;
use strum::VariantNames;
use strum_macros::{EnumString, VariantNames};

pub use error::ParserError;

mod error;

/// The [`Destination`] portion of a [`Instruction::Compute`].
///
/// Represents where the value of a C-instruction should be stored. There are 8
/// possibilities, one of which is [`Destination::None`]. In their binary
/// representation, the first bit is whether or not to store in the `A`
/// register, the second bit is whether or not to store in the `D` register,
/// the third bit is whether or not to store in `RAM[A]`.
#[derive(VariantNames, EnumString, strum_macros::Display)]
pub enum Destination {
    /// Store in: `RAM[A]`.
    #[strum(to_string = "M")]
    M,
    /// Store in: `D` register.
    #[strum(to_string = "D")]
    D,
    /// Store in: `D` register and `RAM[A]`.
    #[strum(to_string = "DM", serialize = "MD")]
    DM,
    /// Store in: `A` register.
    #[strum(to_string = "A")]
    A,
    /// Store in: `A` register and `RAM[A]`.
    #[strum(to_string = "AM", serialize = "MA")]
    AM,
    /// Store in: `A` register and `D` register.
    #[strum(to_string = "AD", serialize = "DA")]
    AD,
    /// Store in: `A` register, `D` register, and `RAM[A]`.
    #[strum(
        to_string = "ADM",
        serialize = "AMD",
        serialize = "MAD",
        serialize = "MDA",
        serialize = "DMA",
        serialize = "DAM"
    )]
    ADM,
    /// The value is not stored.
    #[strum(to_string = "")]
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
#[derive(VariantNames, EnumString, strum_macros::Display)]
pub enum Compute {
    /// Compute: `0`.
    #[strum(to_string = "0")]
    Zero,
    /// Compute: `1`.
    #[strum(to_string = "1")]
    One,
    /// Compute: `-1`.
    #[strum(to_string = "-1")]
    NegativeOne,
    /// Compute: the value in the `D` register.
    #[strum(to_string = "D")]
    D,
    /// Compute: the value in the `A` register.
    #[strum(to_string = "A")]
    A,
    /// Compute: the value in `RAM[A]`.
    #[strum(to_string = "M")]
    M,
    /// Compute: bitwise negation of the value in the `D` register.
    #[strum(to_string = "!D")]
    NotD,
    /// Compute: bitwise negation of the value in the `A` register.
    #[strum(to_string = "!A")]
    NotA,
    /// Compute: bitwise negation of the value in `RAM[A]`.
    #[strum(to_string = "!M")]
    NotM,
    /// Compute: arithmetic negation of the value in the `D` register.
    #[strum(to_string = "-D")]
    NegativeD,
    /// Compute: arithmetic negation of the value in the `A` register.
    #[strum(to_string = "-A")]
    NegativeA,
    /// Compute: arithmetic negation of the value in `RAM[A]`.
    #[strum(to_string = "-M")]
    NegativeM,
    /// Compute: the value in the `D` register plus `1`.
    #[strum(to_string = "D+1", serialize = "1+D")]
    DPlusOne,
    /// Compute: the value in the `A` register plus `1`.
    #[strum(to_string = "A+1", serialize = "1+A")]
    APlusOne,
    /// Compute: the value in `RAM[A]` plus `1`.
    #[strum(to_string = "M+1", serialize = "1+M")]
    MPlusone,
    /// Compute: the value in the `D` register minus `1`.
    #[strum(to_string = "D-1")]
    DMinusOne,
    /// Compute: the value in the `A` register minus `1`.
    #[strum(to_string = "A-1")]
    AMinusOne,
    /// Compute: the value in `RAM[A]` minus `1`.
    #[strum(to_string = "M-1")]
    MMinusOne,
    /// Compute: the value in the `D` register plus the value in the `A`
    /// register.
    #[strum(to_string = "D+A", serialize = "A+D")]
    DPlusA,
    /// Compute: the value in the `D` register plus the value in `RAM[A]`.
    #[strum(to_string = "D+M", serialize = "M+D")]
    DPlusM,
    /// Compute: the value in the `D` register minus the value in the `A`
    /// register.
    #[strum(to_string = "D-A")]
    DMinusA,
    /// Compute: the value in the `D` register minus the value in `RAM[A]`.
    #[strum(to_string = "D-M")]
    DMinusM,
    /// Compute: the value in the `A` register minus the value in the `D`
    /// register.
    #[strum(to_string = "A-D")]
    AMinusD,
    /// Compute: the value in `RAM[A]` minus the value in the `D` register.
    #[strum(to_string = "M-D")]
    MMinusD,
    /// Compute: the bitwise AND of the value in the `D` register and the value
    /// in the `A` register.
    #[strum(to_string = "D&A", serialize = "A&D")]
    DAndA,
    /// Compute: the bitwise AND of the value in the `D` register and the value
    /// in `RAM[A]`.
    #[strum(to_string = "D&M", serialize = "M&D")]
    DAndM,
    /// Compute: the bitwise OR of the value in the `D` register and the value
    /// in the `A` register.
    #[strum(to_string = "D|A", serialize = "A|D")]
    DOrA,
    /// Compute: the bitwise OR of the value in the `D` register and the value
    /// in `RAM[A]`.
    #[strum(to_string = "D|M", serialize = "M|D")]
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
#[derive(VariantNames, EnumString, strum_macros::Display)]
#[strum(serialize_all = "UPPERCASE")]
pub enum Jump {
    /// Jump if: [`Compute`] > `0`.
    JGT,
    /// Jump if: [`Compute`] == `0`.
    JEQ,
    /// Jump if: [`Compute`] >= `0`.
    JGE,
    /// Jump if: [`Compute`] < `0`.
    JLT,
    /// Jump if: [`Compute`] != `0`.
    JNE,
    /// Jump if: [`Compute`] <= `0`.
    JLE,
    /// Jump.
    JMP,
    /// Don't jump.
    #[strum(to_string = "")]
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
#[derive(Clone)]
pub struct Parser {
    /// The contents of the file as a String.
    file: String,
}

impl Parser {
    /// Returns an [`Iterator`] over the lines of a the held file contents, as
    /// string slices.
    pub fn lines(&self) -> impl Iterator<Item = &str> {
        self.file.lines()
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

/// The two types of [`Instruction`] (and the one pseudo-instruction) supported by
/// the Hack CPU.
pub enum Instruction {
    /// [`Instruction::Address`] represents an A-instruction. The [`String`]
    /// inside should be the symbol or numerical constant that would come after
    /// the `@`.
    ///
    /// Examples:
    /// ```
    /// use hack_assembler::parser::Instruction;
    ///
    /// // @1984
    /// Instruction::Address("1984".into());
    /// // @my_var
    /// Instruction::Address("my_var".into());
    /// ```
    Address(String),
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
    /// The highest valid memory address in the Hack computer.
    pub const MAX_VALID_MEMORY_ADDRESS: u16 = 0x6000;

    /// Attempts to parse a [`Instruction::Label`] from a string.
    fn try_parse_label(label: &str) -> Result<Instruction, ParserError> {
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

    /// Attempts to parse an [`Instruction::Address`] from a string.
    fn try_parse_address(address: &str) -> Result<Instruction, ParserError> {
        let address: &str = &address[1..];
        match address {
            address if Self::is_allowed_constant(address) => {
                Ok(Self::Address(address.into()))
            }
            symbol if Instruction::is_allowed_symbol(symbol) => {
                Ok(Self::Address(symbol.into()))
            }
            _ => Err(ParserError::InvalidAddress),
        }
    }

    /// Attempts to parse a [`Instruction::Compute`] from a string.
    fn try_parse_compute(compute: &str) -> Result<Instruction, ParserError> {
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
    /// notation. They should not exceed [`Self::MAX_VALID_MEMORY_ADDRESS`].
    fn is_allowed_constant(string: &str) -> bool {
        !string.is_empty()
            && !string.contains(|character: char| !(character.is_ascii_digit()))
            && string <= format!("{}", Self::MAX_VALID_MEMORY_ADDRESS).as_str()
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
            Self::Address(address) => write!(f, "{address}"),
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
        let less: String =
            format!("{}", Instruction::MAX_VALID_MEMORY_ADDRESS - 1);
        let max: String = format!("{}", Instruction::MAX_VALID_MEMORY_ADDRESS);
        let more: String =
            format!("{}", Instruction::MAX_VALID_MEMORY_ADDRESS + 1);
        assert!(less < max);
        assert!(less < more);
        assert!(max > less);
        assert!(max < more);
        assert!(more > less);
        assert!(more > max);

        assert!(Instruction::is_allowed_constant(&less));
        assert!(Instruction::is_allowed_constant(&max));
        assert!(!Instruction::is_allowed_constant(&more));
    }

    #[test]
    fn read_address() {
        let instructions: [&str; 4] = ["@200", "@variable", "@LOOP", "@R16"];
        for instruction in instructions {
            assert!(matches!(
                Instruction::from_str(instruction),
                Ok(Instruction::Address(_))
            ));
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
