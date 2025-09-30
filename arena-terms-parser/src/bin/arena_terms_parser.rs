use anyhow::Result;
use arena_terms::{Arena, Term};
use arena_terms_parser::parser::TermParser;
use clap::{Parser as ClapParser, Subcommand};
use parlex::{Lexer, Parser};
use smartstring::alias::String;
use std::io::{self, BufReader, Read};
use std::iter::FusedIterator;
use std::mem;

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
        /// Input file with operator definitions
        #[arg(short, long)]
        defs: Option<String>,
        /// Input file with terms
        #[arg(short, long)]
        terms: String,
    },
    /// Prints sizes
    Sizes {},
}

fn open_input(path: &str) -> Result<impl FusedIterator<Item = u8>> {
    let iter = BufReader::new(std::fs::File::open(path)?)
        .bytes()
        .map(Result::unwrap)
        .fuse();

    Ok(iter)
}

fn main() -> Result<()> {
    env_logger::init();

    let args = Args::parse();

    match args.command {
        Commands::Parse {
            defs: defs_path,
            terms: terms_path,
        } => {
            let mut arena = Arena::new();
            let mut parser = TermParser::try_new(open_input(&terms_path)?, None)?;
            if let Some(defs_path) = defs_path {
                parser.define_opers(&mut arena, open_input(&defs_path)?, None)?;
            }
            while let Some(tok) = parser.try_next(&mut arena)? {
                println!("{}.", Term::try_from(tok.value)?.display(&arena));
                log::info!(
                    "Stats: {:?}, {:?}",
                    parser.ctx().lexer.stats(),
                    parser.stats()
                );
            }
        }
        Commands::Sizes {} => {
            println!("Size of Term: {}", mem::size_of::<Term>());
            println!("Size of Option<Term>: {}", mem::size_of::<Option<Term>>());
            println!("Size of String: {}", mem::size_of::<String>());
            println!(
                "Size of Option<String>: {}",
                mem::size_of::<Option<String>>()
            );
            println!(
                "Size of std::string::String: {}",
                mem::size_of::<std::string::String>()
            );
            println!(
                "Size of Option<std::string::String>: {}",
                mem::size_of::<Option<std::string::String>>()
            );
        }
    }

    Ok(())
}
