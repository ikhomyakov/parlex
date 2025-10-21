//! # Command-Line Interface (CLI) for `parlex-calc`
//!
//! This binary provides a lightweight interactive interface for the calculator
//! engine defined in the `parlex-calc` crate.
//!
//! It wraps the [`CalcParser`] and uses a [`SymTab`] as an evaluation context,
//! allowing users to parse and evaluate arithmetic expressions from **standard
//! input** or from **files** (via redirected input). Results are printed for
//! inspection and debugging purposes.
//!
//! ## Overview
//! - Reads UTF-8 input from standard input (`stdin`).
//! - Tokenizes and parses expressions using [`CalcParser`].
//! - Evaluates statements (assignments, arithmetic expressions, etc.).
//! - Dumps both the symbol table (`SymTab`) and parsed results to the console.
//!
//! ## Example Usage
//! ```bash
//! $ echo "x = 2; y = x * 5 + 3; y - 1;" | cargo run -- parse
//! ```
//!
//! Output (debug format):
//! ```text
//! [parlex-calc/src/main.rs:87:13] &parser.stats() = (
//!     LexerStats {
//!         unreads: 55,
//!         chars: 29,
//!         matches: 30,
//!     },
//!     ParserStats {
//!         tokens: 18,
//!         shifts: 13,
//!         reductions: 13,
//!         ambigs: 1,
//!     },
//! )
//! [parlex-calc/src/main.rs:88:13] &symtab = SymTab {
//!     tab: {
//!         "x": 2,
//!         "y": 13,
//!     },
//! }
//! [parlex-calc/src/main.rs:89:13] &toks = [
//!     CalcToken {
//!         token_id: Stat,
//!         value: Number(
//!             2,
//!         ),
//!         span: Some(
//!             Span {
//!                 start: Position {
//!                     line: 0,
//!                     column: 0,
//!                 },
//!                 end: Position {
//!                     line: 0,
//!                     column: 5,
//!                 },
//!             },
//!         ),
//!     },
//!     CalcToken {
//!         token_id: Stat,
//!         value: Number(
//!             13,
//!         ),
//!         span: Some(
//!             Span {
//!                 start: Position {
//!                     line: 0,
//!                     column: 7,
//!                 },
//!                 end: Position {
//!                     line: 0,
//!                     column: 20,
//!                 },
//!             },
//!         ),
//!     },
//!     CalcToken {
//!         token_id: Stat,
//!         value: Number(
//!             12,
//!         ),
//!         span: Some(
//!             Span {
//!                 start: Position {
//!                     line: 0,
//!                     column: 22,
//!                 },
//!                 end: Position {
//!                     line: 0,
//!                     column: 27,
//!                 },
//!             },
//!         ),
//!     },
//!     CalcToken {
//!         token_id: Stat,
//!         value: None,
//!         span: Some(
//!             Span {
//!                 start: Position {
//!                     line: 1,
//!                     column: 0,
//!                 },
//!                 end: Position {
//!                     line: 1,
//!                     column: 0,
//!                 },
//!             },
//!         ),
//!     },
//! ]
//! ```
//!
//! ## Command Structure
//!
//! | Command | Description              |
//! |----------|--------------------------|
//! | `parse`  | Reads input and parses it |
//!
//! ## Implementation Notes
//! - Uses [`clap`] for argument parsing.
//! - Leverages [`IterInput`] from `try_next` to stream bytes from `stdin`.
//! - Relies on [`env_logger`] for structured test-friendly logging.
//!
//! [`CalcParser`]: parlex_calc::CalcParser
//! [`SymTab`]: parlex_calc::SymTab
//! [`clap`]: https://crates.io/crates/clap
//! [`env_logger`]: https://crates.io/crates/env_logger
//! [`IterInput`]: try_next::IterInput

use clap::{Parser as ClapParser, Subcommand};
use parlex_calc::{CalcParser, SymTab};
use std::io::Read;
use try_next::{IterInput, TryNextWithContext};

#[derive(ClapParser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Command
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Parses terms
    Parse {},
}

fn open_input() -> std::io::Result<impl Iterator<Item = u8>> {
    let iter = std::io::stdin().lock().bytes().map(Result::unwrap);
    Ok(iter)
}

fn main() {
    env_logger::init();

    let args = Args::parse();

    match args.command {
        Commands::Parse {} => {
            let mut symtab = SymTab::new();
            let input = IterInput::from(open_input().expect("can't open stdin"));
            let mut parser = CalcParser::try_new(input).expect("can't create parser");
            let toks = parser
                .try_collect_with_context(&mut symtab)
                .expect("parsing error");
            dbg!(&parser.stats());
            dbg!(&symtab);
            dbg!(&toks);
        }
    }
}
