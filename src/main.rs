// SPDX-FileCopyrightText: Copyright © 2025 hashcatHitman
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # Hack Assembler
//!
//! An assembler that translates programs written in the Hack assembly language
//! into Hack binary code. Based on the nand2tetris course.

#![feature(strict_provenance_lints, unqualified_local_imports)]

use std::{env, process};

use hack_assembler::{Config, run};
use {strum as _, strum_macros as _};

/// The entrypoint of the assembler executable.
fn main() {
    let args: env::Args = env::args();

    let config: Config = Config::build(args).unwrap_or_else(|error| {
        eprintln!("Problem parsing arguments: {error}");
        process::exit(1);
    });

    if let Err(error) = run(&config) {
        eprintln!("Problem running: {error}");
        process::exit(1);
    }
}
