//! # Hack Assembler
//!
//! `hack-assembler` is a crate providing an assembler that translates programs
//! written in the Hack assembly language into Hack binary code. Based on the
//! nand2tetris course.

/// Adds left and right together, returning the sum.
pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
