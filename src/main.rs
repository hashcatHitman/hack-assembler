//! # Hack Assembler
//!
//! An assembler that translates programs written in the Hack assembly language
//! into Hack binary code. Based on the nand2tetris course.

use hack_assembler::parser::{Instruction, ParserError};
use std::str::FromStr;

/// The entrypoint of the assembler executable.
fn main() {
    println!("Hack the planet!");
    let instructions: [&str; 5] =
        [" (wow)\n", "@var", "@100", "\tADM=M-1;JNE", "fail"];

    for instruction in instructions {
        let instruction: Result<Instruction, ParserError> =
            Instruction::from_str(instruction);
        match instruction {
            Ok(Instruction::Address(instruction)) => {
                println!(
                    "Found address: {}",
                    Instruction::Address(instruction)
                );
            }
            Ok(Instruction::Label(instruction)) => {
                println!("Found label: {}", Instruction::Label(instruction));
            }
            Ok(Instruction::Compute(d, c, j)) => {
                println!("Found compute: {}", Instruction::Compute(d, c, j));
            }
            Err(error) => eprintln!("{error}"),
        }
    }
}
