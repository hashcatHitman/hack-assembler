// SPDX-FileCopyrightText: Copyright © 2025 hashcatHitman
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # Hack Assembler
//!
//! An assembler that translates programs written in the Hack assembly language
//! into Hack binary code. Based on the nand2tetris course.

#![feature(
    strict_provenance_lints,
    unqualified_local_imports,
    must_not_suspend,
    iterator_try_collect
)]

use std::env;

use hack_assembler::{Config, run};
use {strum as _, strum_macros as _};

/// The entrypoint of the assembler executable.
// allow instead of expect due to:
// https://github.com/rust-lang/rust-clippy/issues/14491
#[allow(clippy::missing_errors_doc, reason = "I'll finish the docs later.")]
fn main() -> Result<(), u8> {
    let args: env::Args = env::args();

    let config: Config = match Config::build(args) {
        Ok(config) => config,
        Err(error) => {
            eprintln!("Problem parsing arguments: {error}");
            return Err(1);
        }
    };

    match run(&config) {
        Ok(ok) => Ok(ok),
        Err(error) => {
            eprintln!("Problem running: {error}");
            Err(1)
        }
    }
}
