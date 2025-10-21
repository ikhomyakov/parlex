//! # parlex-calc
//!
//! A small demonstration crate built on **parlex**, providing a complete,
//! minimal example of a lexer–parser pipeline for a calculator language.
//!
//! This crate showcases how to connect a [`CalcLexer`] and [`CalcParser`]
//! using token spans and a shared symbol table. It’s intended for educational
//! and testing purposes rather than production use.
//!
//! ## Overview
//!
//! The `parlex-calc` crate defines the following components:
//!
//! - [`lexer`] — a tokenizing module that converts raw input into a stream of
//!   [`CalcToken`] items, each annotated with a [`Span`] indicating its
//!   position in the source text.
//! - [`parser`] — a grammar-based parser that consumes lexer tokens to produce
//!   an abstract syntax tree (AST) or evaluate expressions directly.
//! - [`symtab`] — a symbol table abstraction ([`SymTab`]) that manages variable
//!   bindings and supports expression evaluation.
//! - [`token`] — shared token definitions, including [`CalcToken`],
//!   [`TokenValue`], and [`TokenID`].
//!
//! ## Example
//!
//! ```rust
//! use try_next::{IterInput, TryNextWithContext};
//! use parlex::span;
//! use parlex_calc::{CalcParser, CalcToken, SymTab, TokenID, TokenValue};
//!
//! // Input source string
//! let source = "a = 1 + 2 * 3";
//!
//! // Initialize parser
//!
//! let mut symtab = SymTab::new();
//! let input = IterInput::from(source.bytes());
//! let mut parser = CalcParser::try_new(input).unwrap();
//!
//! // Run the lexer–parser pipeline
//! let Ok(Some(token)) = parser.try_next_with_context(&mut symtab) else {panic!("expected token")};
//! assert!(matches!(
//!     token,
//!     CalcToken {
//!         token_id: TokenID::Stat,
//!         span: span!(0, 0, 0, 13),
//!         value: TokenValue::Number(7)
//!     }
//! ));
//! ```
//!
//! ## Modules
//!
//! - [`lexer`] — lexical analysis (tokenization)
//! - [`parser`] — grammar-based parsing
//! - [`symtab`] — symbol table and evaluation context
//! - [`token`] — token definitions and span utilities
//!
//! ## Re-exports
//!
//! To simplify integration, the crate re-exports its main entry points:
//!
//! ```text
//! CalcLexer, CalcLexerDriver, CalcParser, CalcParserDriver,
//! SymTab, SymTabError, CalcToken, TokenValue, TokenID
//! ```
//!
//! These are the primary types needed to embed `parlex-calc` in tests,
//! examples, or small interpreters.
pub mod lexer;
pub mod parser;
pub mod symtab;
pub mod token;

pub use lexer::{CalcLexer, CalcLexerDriver};
pub use parser::parser_data::TokenID;
pub use parser::{CalcParser, CalcParserDriver};
pub use symtab::{SymTab, SymTabError};
pub use token::{CalcToken, TokenValue};
