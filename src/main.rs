//! # Hack Assembler
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
//! An assembler that translates programs written in the Hack assembly language
//! into Hack binary code. Based on the nand2tetris course.

use hack_assembler::parser::{Code, Instruction, ParserError};
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
            Ok(
                instruction @ (Instruction::AddressLiteral(_)
                | Instruction::AddressSymbolic(_)),
            ) => {
                println!(
                    "Found address: {} with code {}",
                    instruction,
                    instruction.code()
                );
            }
            Ok(instruction @ Instruction::Label(_)) => {
                println!(
                    "Found label: {} with code {}",
                    instruction,
                    instruction.code()
                );
            }
            Ok(instruction @ Instruction::Compute(..)) => {
                println!(
                    "Found compute: {} with code {}",
                    instruction,
                    instruction.code()
                );
            }
            Err(error) => eprintln!("{error}"),
        }
    }
}
