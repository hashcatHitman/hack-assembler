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
//! `hack-assembler` is a crate providing an assembler that translates programs
//! written in the Hack assembly language into Hack binary code. Based on the
//! nand2tetris course.

#![feature(strict_provenance_lints, unqualified_local_imports)]

pub mod parser;
