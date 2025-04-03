//! # Hack Assembler
//!
//! An assembler that translates programs written in the Hack assembly language
//! into Hack binary code. Based on the nand2tetris course.

/// The entrypoint of the assembler executable.
fn main() {
    let left: u64 = 42;
    let right: u64 = 16;
    let sum: u64 = hack_assembler::add(left, right);
    println!("{left} + {right} = {sum}");
    println!("Hack the planet!");
}
