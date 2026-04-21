# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Test Commands

```bash
cargo build                    # build all crates
cargo test                     # run all tests
cargo test -p parlex           # test a single crate
cargo test test_name           # run a single test by name
cargo test -- --nocapture      # run tests with stdout
cargo clippy                   # lint
```

Run the calculator example:
```bash
echo "x = 2 + 3; y = x * 4;" | cargo run -p parlex-calc -- parse
```

## Architecture

Parlex is a Rust lex/yacc-style toolchain with clean separation between generated code and user code. Grammar rules and lexer definitions are named explicitly; user code refers to them by name rather than embedding code in spec files.

**Three crates:**

- **parlex** — Core runtime library. Defines traits (`LexerData`, `LexerDriver`, `ParserData`, `ParserDriver`, `Token`) and data structures (`Lexer`, `Parser`, `LexerCursor`, `Span`, `Position`) that generated and user code depend on.
- **parlex-gen** — Code generators invoked at build time via `build.rs`:
  - **ALEX** — Lexer generator. Reads `.alex` spec files, builds DFAs via `regex-automata`, produces Rust implementing `LexerData`/`LexerDriver`.
  - **ASLR** — Parser generator. Reads `.g` grammar files, builds SLR(1) action/goto tables, produces Rust implementing `ParserData`/`ParserDriver`.
- **parlex-calc** — Working example calculator demonstrating the full pipeline.

**Code generation flow:** `.alex` and `.g` spec files → `build.rs` calls `parlex_gen::alex::generate()` and `parlex_gen::aslr::generate()` → generated Rust files in `OUT_DIR` → included via `include!()` at compile time. Never edit generated files directly.

**Trait-based design:** Users implement `LexerDriver` (token assembly from matched rules) and `ParserDriver` (reductions, ambiguity resolution) to hook into generated code. Both lexer and parser implement `TryNextWithContext` from the external `try-next` crate for streaming consumption.

**Key design choice — dynamic ambiguity resolution:** Unlike yacc/bison which resolve shift/reduce conflicts statically, ASLR supports runtime resolution via `ParserDriver::resolve_ambig`, enabling languages like Prolog where operator definitions change at runtime.

## Encoding

Parlex is encoding-agnostic — the lexer operates on raw bytes. Encoding handling (UTF-8 validation, Latin1 transcoding, etc.) is done in `LexerDriver` action callbacks, not in the core library.

## Workspace

- Rust edition 2024, minimum rust-version 1.89
- License: MIT
- Uses `smartstring` for efficient short string storage in tokens
