//! Command-line interface (CLI) for the parlex-calc
//!
//! This binary wraps the [`CalcParser`] and exposes a simple command-line interface
//! for parsing Prolog-like terms backed by an [`Arena`] bump-allocator.
//! It allows reading term input from standard input or files, parsing them
//! into compact arena-allocated term representations, and printing or inspecting
//! the results.
//!
//! [`TermParser`]: arena_terms_parser::parser::TermParser
//! [`parser_oper_defs`]: arena_terms_parser::parser::parser_oper_defs
//! [`Arena`]: arena_terms::Arena

use clap::{Parser as ClapParser, Subcommand};
use parlex_calc::{CalcParser, IterInput, SymTab};
use smartstring::alias::String;
use std::io::{BufReader, Read};
use try_next::TryNextWithContext;

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
    Parse {
        /// Input file with parlex-calc statements
        #[arg(short, long)]
        input: String,
    },
}

fn open_input(path: &str) -> std::io::Result<impl Iterator<Item = u8>> {
    let iter = BufReader::new(std::fs::File::open(path)?)
        .bytes()
        .map(Result::unwrap);
    Ok(iter)
}

fn main() {
    env_logger::init();

    let args = Args::parse();

    match args.command {
        Commands::Parse { input: path } => {
            let mut symtab = SymTab::new();
            let input =
                IterInput::from(open_input(&path).expect(&format!("can't open {:?}", path)));
            let mut parser = CalcParser::try_new(input).expect("can't create parser");
            let toks = parser
                .try_collect_with_context(&mut symtab)
                .expect("parsing error");
            dbg!(&symtab);
            dbg!(&toks);
        }
    }
}
