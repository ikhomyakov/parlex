//! Copyright (c) 2005–2025 IKH Software, Inc.
//!
//! Released under the terms of the GNU Lesser General Public License, version 3.0
//! or (at your option) any later version (LGPL-3.0-or-later).
//!
//! Parser for arena-backed Prolog-like terms.
//!
//! This crate provides a parser for parsing Prolog-style terms into the
//! compact bump‑allocated arena representation from the [`arena_terms`] crate.
//! It is built on top of the `parlex` runtime library and uses the [`parlex-gen`]
//! `alex` and `aslr` code generation tools.
//!
//! Key components:
//! - `lexer`: tokenization and value extraction (atoms, numbers, dates, etc.)
//! - `oper`: operator fixity/precedence/associativity and definitions
//! - `parser`: SLR parser that yields `arena_terms::Term` values
//!
//! # Crates.io
//! Published at [crates.io/crates/arena-terms-parser](https://crates.io/crates/arena-terms-parser).

pub mod lexer;
pub mod oper;
pub mod parser;
