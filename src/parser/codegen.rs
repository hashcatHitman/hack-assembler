// SPDX-FileCopyrightText: Copyright © 2025 hashcatHitman
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # Hack Codegen
//!
//! The codegen module defines and implements the traits [`Code`] and
//! [`AutoCode`], which are implemented for types which can be parsed into
//! opcodes (or parts of opcodes) for the Hack computer - namely,
//! [`Instruction`] and its components.

use strum::EnumProperty;

use super::{Compute, Destination, HackError, Instruction, Jump};

/// A trait implemented by any type which can be parsed into opcodes (or parts
/// of opcodes) for the Hack computer.
pub trait Code {
    /// Returns the opcode representative of this implementor of [`Code`], as a
    /// binary String.
    #[expect(
        clippy::missing_errors_doc,
        reason = "I'll finish the docs later."
    )]
    fn code(&self) -> Result<String, HackError>;
}

/// A trait which provides a blanket implementation of [`Code`] for any type
/// which implements it.
///
/// # Panics
///
/// It is assumed that implementors of this trait will be enums which implement
/// [`EnumProperty`] and have a property called "code" on each variant
/// containing the appropriate opcode String for that variant. If any variants
/// are missing this property, [`Code::code`] will panic!
trait AutoCode: EnumProperty {
    /// A constant meant to hold the identifier of the implementing enum, for
    /// use in panics.
    const SELF: &str;
}

impl<T: AutoCode> Code for T {
    /// Returns the opcode representative of this implementor of [`Code`], as a
    /// binary String.
    ///
    /// # Panics
    ///
    /// It is assumed that implementors of this trait will be enums which
    /// implement [`EnumProperty`] and have a property called "code" on each
    /// variant containing the appropriate opcode String for that variant. If
    /// any variants are missing this property, this method will panic!
    fn code(&self) -> Result<String, HackError> {
        const TEMPLATE: &str =
            "missing a codegen property for one or more of the variants of ";

        let error: String = format!("{}{}", TEMPLATE, <Self as AutoCode>::SELF);

        self.get_str("code")
            .map_or(Err(HackError::WriteError(error)), |code| {
                Ok(code.to_owned())
            })
    }
}

impl AutoCode for Compute {
    const SELF: &str = "Compute";
}

impl AutoCode for Destination {
    const SELF: &str = "Destination";
}

impl AutoCode for Jump {
    const SELF: &str = "Jump";
}

impl Code for Instruction {
    fn code(&self) -> Result<String, HackError> {
        match *self {
            Self::AddressLiteral(address) => Ok(format!("0{address:015b}")),
            Self::AddressSymbolic(_) => {
                todo!("TODO: Needs symbol table.")
            }
            Self::Compute(destination, compute, jump) => Ok(format!(
                "111{}{}{}",
                compute.code()?,
                destination.code()?,
                jump.code()?
            )),
            Self::Label(_) => todo!("TODO: Needs symbol table."),
        }
    }
}

#[cfg(test)]
#[expect(clippy::missing_panics_doc, reason = "tests")]
mod tests {

    use strum::IntoEnumIterator;

    use super::*;

    fn codegen_from_arrays(instructions: &[Instruction], codes: &[&str]) {
        for (index, instruction) in instructions.iter().enumerate() {
            assert!(instruction.code().unwrap() == codes[index]);
        }
    }

    fn codegen_from_iter<Enum>(codes: &[&str])
    where
        Enum: IntoEnumIterator + Code,
    {
        for (index, variant) in Enum::iter().enumerate() {
            assert!(variant.code().unwrap() == codes[index]);
        }
    }

    #[test]
    fn codegen_compute() {
        const CODES: [&str; 28] = [
            "0101010", "0111111", "0111010", "0001100", "0110000", "1110000",
            "0001101", "0110001", "1110001", "0001111", "0110011", "1110011",
            "0011111", "0110111", "1110111", "0001110", "0110010", "1110010",
            "0000010", "1000010", "0010011", "1010011", "0000111", "1000111",
            "0000000", "1000000", "0010101", "1010101",
        ];
        codegen_from_iter::<Compute>(&CODES);
    }

    #[test]
    fn codegen_destination() {
        const CODES: [&str; 8] =
            ["001", "010", "011", "100", "101", "110", "111", "000"];
        codegen_from_iter::<Destination>(&CODES);
    }

    #[test]
    fn codegen_jump() {
        const CODES: [&str; 8] =
            ["001", "010", "011", "100", "101", "110", "111", "000"];
        codegen_from_iter::<Jump>(&CODES);
    }

    #[test]
    fn code_gen_compute_instruction() {
        const CODES: [&str; 8] = [
            "1110111111001000", // M=1
            "1110101010001000", // M=0
            "1111110000010000", // D=M
            "1111010011010000", // D=D-M
            "1110001100000001", // D;JGT
            "1111000010001000", // M=D+M
            "1111110111001000", // M=M+1
            "1110101010000111", // 0;JMP
        ];
        const INSTRUCTIONS: [Instruction; 8] = [
            Instruction::Compute(Destination::M, Compute::One, Jump::None),
            Instruction::Compute(Destination::M, Compute::Zero, Jump::None),
            Instruction::Compute(Destination::D, Compute::M, Jump::None),
            Instruction::Compute(Destination::D, Compute::DMinusM, Jump::None),
            Instruction::Compute(Destination::None, Compute::D, Jump::JGT),
            Instruction::Compute(Destination::M, Compute::DPlusM, Jump::None),
            Instruction::Compute(Destination::M, Compute::MPlusOne, Jump::None),
            Instruction::Compute(Destination::None, Compute::Zero, Jump::JMP),
        ];

        codegen_from_arrays(&INSTRUCTIONS, &CODES);
    }

    #[test]
    fn codegen_address_literal() {
        const CODES: [&str; 17] = [
            "0000000000000000", // @0
            "0000000000000001", // @1
            "0000000000000010", // @2
            "0000000000000100", // @4
            "0000000000001000", // @8
            "0000000000010000", // @16
            "0000000000100000", // @32
            "0000000001000000", // @64
            "0000000010000000", // @128
            "0000000100000000", // @256
            "0000001000000000", // @512
            "0000010000000000", // @1024
            "0000100000000000", // @2048
            "0001000000000000", // @4096
            "0010000000000000", // @8192
            "0100000000000000", // @16384
            "0111111111111111", // @32767
        ];

        const INSTRUCTIONS: [Instruction; 17] = [
            Instruction::AddressLiteral(0x0000), // Minimum valid
            Instruction::AddressLiteral(0x0001),
            Instruction::AddressLiteral(0x0002),
            Instruction::AddressLiteral(0x0004),
            Instruction::AddressLiteral(0x0008),
            Instruction::AddressLiteral(0x0010),
            Instruction::AddressLiteral(0x0020),
            Instruction::AddressLiteral(0x0040),
            Instruction::AddressLiteral(0x0080),
            Instruction::AddressLiteral(0x0100),
            Instruction::AddressLiteral(0x0200),
            Instruction::AddressLiteral(0x0400),
            Instruction::AddressLiteral(0x0800),
            Instruction::AddressLiteral(0x1000),
            Instruction::AddressLiteral(0x2000),
            Instruction::AddressLiteral(0x4000),
            Instruction::AddressLiteral(0x7FFF), // Maximum valid
        ];

        codegen_from_arrays(&INSTRUCTIONS, &CODES);
    }

    #[test]
    fn codegen_address_symbolic() {
        todo!("TODO: Needs symbol table.");
    }

    #[test]
    fn codegen_label() {
        todo!("TODO: Needs symbol table.");
    }
}
