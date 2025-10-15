/// Includes the generated lexer definition produced by **`parlex-gen`**’s
/// [`alex`](https://crates.io/crates/parlex-gen) tool.
///
/// The included file (`lexer_data.rs`) contains the DFA tables, mode definitions,
/// and rule implementations required for the [`TermLexer`]. It is generated at
/// build time by the project’s `build.rs` script.
pub mod lexer_data {
    include!(concat!(env!("OUT_DIR"), "/lexer_data.rs"));
}

/// Includes the generated SLR parser tables and definitions.
///
/// This file (`parser_data.rs`) is produced by the **parlex-gen** [`aslr`] tool
/// during the build process. It defines the parsing automaton, rule metadata,
/// and associated enum types used by the [`TermParser`].
pub mod parser_data {
    include!(concat!(env!("OUT_DIR"), "/parser_data.rs"));
}

use crate::{SymTab, SymTabError};
use lexer_data::{LexData, Mode, Rule};
use parlex::{
    Lexer, LexerData, LexerDriver, LexerError, Parser, ParserAction, ParserData, ParserDriver,
    ParserError, Token,
};
use parser_data::{AmbigID, ParData, ProdID, StateID, TokenID};
use std::convert::Infallible;
use std::iter::Fuse;
use std::marker::PhantomData;
use thiserror::Error;
use try_next::TryNextWithContext;

/// Represents all possible errors that can occur within the calculator.
///
/// The [`CalcError`] enum aggregates various error sources encountered
/// during lexical analysis, parsing, and symbol-table operations.
/// It implements [`std::error::Error`] via [`thiserror::Error`], allowing
/// ergonomic error propagation with the `?` operator.
///
/// Each variant wraps a more specific underlying error type.
///
/// # Variants
///
/// - [`CalcError::ParseInt`]:
///   Returned when a numeric literal cannot be parsed into an integer,
///   typically originating from [`std::num::ParseIntError`].
///
/// - [`CalcError::FromUtf8`]:
///   Returned when the input contains invalid UTF-8 byte sequences and
///   cannot be decoded into a [`String`].
///
/// - [`CalcError::SymTab`]:
///   Wraps an error from the symbol table subsystem ([`SymTabError`]).
///
/// # Example
/// ```rust
/// # use parlex_calc::{CalcError, SymTabError};
/// # use std::str::FromStr;
/// // Example of a parse error bubbling up as CalcError::ParseInt
/// let result: Result<i64, CalcError> = i64::from_str("notanumber").map_err(CalcError::from);
/// assert!(matches!(result.unwrap_err(), CalcError::ParseInt(_)));
///
/// // Example of a symbol-table error propagation
/// let sym_err = SymTabError::InvalidIndex { index: 10, len: 3 };
/// let err = CalcError::from(sym_err);
/// assert!(matches!(err, CalcError::SymTab(_)));
/// ```
#[derive(Debug, Error)]
pub enum CalcError {
    /// An integer literal could not be parsed from its string representation.
    ///
    /// Typically originates from [`std::num::ParseIntError`].
    #[error("unable to parse {0:?}")]
    ParseInt(#[from] std::num::ParseIntError),

    /// Failed to decode UTF-8 bytes from input.
    ///
    /// Wraps a [`std::string::FromUtf8Error`].
    #[error("utf8 error {0:?}")]
    FromUtf8(#[from] std::string::FromUtf8Error),

    /// A symbol-table operation failed.
    ///
    /// Wraps a [`SymTabError`] produced by symbol-table lookups or updates.
    #[error("symtab error {0:?}")]
    SymTab(#[from] SymTabError),
}

/// An input adapter that wraps any iterator and provides a `TryNextWithContext`
/// interface, automatically fusing the iterator so it never yields items
/// after returning `None` once.
///
/// # Type Parameters
///
/// - `I`: The underlying iterator type. It can be any `Iterator`.
/// - `C`: The *context* type, which is passed by mutable reference to each
///   `try_next_with_context` call.
pub struct IterInput<I, C>
where
    I: Iterator,
{
    /// The underlying fused iterator.
    iter: Fuse<I>,

    /// Marker to make the type invariant in `C` and tie its lifetime logically
    /// to the context without owning it.
    _marker: PhantomData<fn(C)>,
}

impl<I, C> IterInput<I, C>
where
    I: Iterator,
{
    /// Creates a new `IterInput` from any iterator.
    ///
    /// The iterator is automatically fused internally, so that once it returns
    /// `None`, all further `next()` calls will also return `None`.
    pub fn from(iter: I) -> Self {
        Self {
            iter: iter.fuse(),
            _marker: PhantomData,
        }
    }
}

impl<I, C> TryNextWithContext for IterInput<I, C>
where
    I: Iterator,
{
    type Item = I::Item;
    type Error = Infallible;
    type Context = C;

    #[inline]
    fn try_next_with_context(
        &mut self,
        _context: &mut Self::Context,
    ) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self.iter.next())
    }
}

/// Represents the value carried by a lexical token.
///
/// Each token in the lexer may carry optional data depending on its kind.
/// For example, identifiers and numbers store extra information such as
/// an index into the symbol table or a literal numeric value.
///
/// This type is used inside a [`CalcToken`] struct alongside a
/// [`TokenID`] indicating what category the token belongs to.
///
/// # Variants
///
/// - [`TokenValue::None`]:
///   Used for tokens that do not carry any extra data (e.g., punctuation, operators).
///
/// - [`TokenValue::Ident(usize)`]:
///   Stores the **symbol table index** of an identifier.
///   The `usize` refers to an entry in a [`SymTab`].
///
/// - [`TokenValue::Number(i64)`]:
///   Represents an integer literal value.
///
/// # Example
/// ```rust
/// # use parlex_calc::TokenValue;
///
/// let ident = TokenValue::Ident(0);
/// let number = TokenValue::Number(42);
/// let punct = TokenValue::None;
///
/// match number {
///     TokenValue::Number(n) => assert_eq!(n, 42),
///     _ => unreachable!(),
/// }
/// ```
#[derive(Debug, Clone)]
pub enum TokenValue {
    /// No associated data (for symbols or keywords).
    None,

    /// Identifier token with an index into the symbol table.
    Ident(usize),

    /// Integer literal token.
    Number(i64),
}

/// A concrete implementation of a lexical token used by the calculator.
///
/// The [`CalcToken`] type represents a single lexical unit (identifier,
/// numeric literal, or operator) recognized by the calculator’s lexer.
/// It implements the generic [`Token`] trait, providing access to its
/// token identifier and source position (line number).
///
/// This structure ties together:
/// - The token’s identifier (via [`TokenID`]),
/// - The token’s **associated data** (via [`TokenValue`]),
/// - The **line number** where it occurs in the input stream.
///
/// # Trait Implementation
///
/// Implements the [`Token`] trait, providing:
/// - [`token_id()`](#method.token_id): returns the token’s [`TokenID`].
/// - [`line_no()`](#method.line_no): returns the source line number.
///
/// # Fields
///
/// - [`token_id`](#structfield.token_id):
///   The category of token (identifier, number, operator, etc.).
///
/// - [`value`](#structfield.value):
///   The token’s associated value — for instance, a symbol-table index
///   or literal number — stored as a [`TokenValue`].
///
/// - [`line_no`](#structfield.line_no):
///   The 1-based line number where the token appears in the source.
///
/// # Example
/// ```rust
/// # use parlex_calc::{CalcToken, TokenID, TokenValue};
/// # use parlex::Token;
/// let token = CalcToken {
///     token_id: TokenID::Number,
///     value: TokenValue::Number(99),
///     line_no: 3,
/// };
///
/// assert_eq!(token.token_id(), TokenID::Number);
/// assert_eq!(token.line_no(), 3);
/// ```
#[derive(Debug, Clone)]
pub struct CalcToken {
    /// The token’s kind or category (e.g. identifier, operator, number).
    pub token_id: TokenID,
    /// The associated value for the token, if applicable.
    pub value: TokenValue,
    /// The line number in the input source where the token occurs.
    pub line_no: usize,
}

impl Token for CalcToken {
    /// The associated identifier type used to classify this token.
    type TokenID = TokenID;

    /// Returns the token’s kind identifier.
    fn token_id(&self) -> Self::TokenID {
        self.token_id
    }

    /// Returns the line number where the token appears.
    fn line_no(&self) -> usize {
        self.line_no
    }
}

/// A stateful driver for the calculator lexer.
///
/// `CalcLexerDriver` orchestrates rule actions emitted by [`Lexer`], keeping
/// minimal state needed during lexing (e.g., nested comment depth).
///
/// The driver is generic over an input source `I` that yields bytes (`u8`)
/// and supports contextual access to a symbol table via
/// [`TryNextWithContext<Item = u8, Context = SymTab>`].
///
/// # State
///
/// - [`comment_level`](#structfield.comment_level):
///   Tracks the current nesting level of block comments. Increment on
///   comment open (e.g. `/*`) and decrement on comment close (e.g. `*/`).
///   Implementations typically skip emitting tokens while `comment_level > 0`.
///
/// - [`_marker`](#structfield._marker):
///   A `PhantomData<I>` marker to bind the generic `I` without storing a value.
///
/// # Associated Types (via `LexerDriver`)
///
/// - `LexerData = LexData` — Tokenization metadata and rule IDs produced by your
///   lexer generator.
/// - `Token = CalcToken` — The concrete token type emitted by the lexer.
/// - `Lexer = Lexer<I, Self>` — The concrete lexer over input `I` driven by this type.
/// - `Error = CalcError` — Unified error type used during lexing.
/// - `Context = I::Context` — External context available to actions (here: `SymTab`).
///
/// # Action Handling
///
/// The [`action`](Self::action) method is invoked whenever the underlying DFA
/// recognizes a rule.
///
/// # Errors
/// This implementation return:
/// - `CalcError::ParseInt` when a numeric literal can’t be parsed,
/// - `CalcError::FromUtf8` for invalid UTF-8 in identifiers/strings,
/// - `CalcError::SymTab` for symbol table failures (e.g., invalid index).
pub struct CalcLexerDriver<I> {
    /// Current nesting depth of block comments.
    ///
    /// - Increment on comment open (e.g., `/*`).
    /// - Decrement on comment close (e.g., `*/`).
    /// - Ensure it never goes negative; reaching EOF with a positive value
    ///   should typically raise a lexical error.
    comment_level: i32,

    /// Marker to bind the driver to the input type `I` without storing it.
    _marker: PhantomData<I>,
}

impl<I> LexerDriver for CalcLexerDriver<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    /// Rule identifiers and metadata produced by the lexer.
    type LexerData = LexData;

    /// Concrete token type emitted by the driver.
    type Token = CalcToken;

    /// Concrete lexer type parameterized by input and driver.
    type Lexer = Lexer<I, Self>;

    /// Unified error type returned by actions.
    type Error = CalcError;

    /// Externally supplied context available to actions (symbol table).
    type Context = I::Context;

    /// Handles a single lexer rule match.
    ///
    /// Called by the lexer when a DFA rule in [`Lexer`] fires. The implementation
    /// typically inspects `rule`, reads the matched span from `lexer`, and either:
    ///
    /// - emits a [`CalcToken`] (e.g., identifiers, numbers, operators),
    /// - updates internal state (e.g., `comment_level`),
    /// - or returns an error if the match is invalid.
    ///
    /// Implementations may also use `context` (a [`SymTab`]) to intern identifiers
    /// and store indices in [`TokenValue::Ident`].
    ///
    /// # Errors
    /// Propagates any lexical, parsing, UTF-8 decoding, or symbol-table errors as
    /// [`CalcError`].
    fn action(
        &mut self,
        lexer: &mut Self::Lexer,
        context: &mut Self::Context,
        rule: <Self::LexerData as LexerData>::LexerRule,
    ) -> Result<(), Self::Error> {
        match rule {
            Rule::Empty => {
                unreachable!()
            }
            Rule::Ident => {
                // <Expr> (?:[a-z_][a-z_A-Z0-9]*)
                let index = context.intern(lexer.take_str()?);
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Ident,
                    line_no: lexer.line_no(),
                    value: TokenValue::Ident(index),
                });
            }
            Rule::Number => {
                // <Expr> (?:[0-9]+)
                let s = lexer.take_str()?;
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Number,
                    line_no: lexer.line_no(),
                    value: TokenValue::Number(s.as_str().parse::<i64>()?),
                });
            }
            Rule::Semicolon => {
                // <Expr> ;
                lexer.yield_token(CalcToken {
                    token_id: TokenID::End,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::Equals => {
                // <Expr> =
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Equals,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::Plus => {
                // <Expr> \+
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Plus,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::Minus => {
                // <Expr> -
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Minus,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::Asterisk => {
                // <Expr> \*
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Asterisk,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::Slash => {
                // <Expr> /
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Slash,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::LeftParen => {
                // <Expr> \(
                lexer.yield_token(CalcToken {
                    token_id: TokenID::LeftParen,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::RightParen => {
                // <Expr> \)
                lexer.yield_token(CalcToken {
                    token_id: TokenID::RightParen,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::CommentBegin => {
                // <Expr,Comment> /\*
                lexer.begin(Mode::Comment);
                self.comment_level += 1;
            }
            Rule::CommentEnd => {
                // <Comment> \*/
                self.comment_level -= 1;
                if self.comment_level == 0 {
                    lexer.begin(Mode::Expr);
                }
            }
            Rule::CommentChar => { // <Comment> .+
            }
            Rule::NewLine => {
                // <*> (?:\n)
                lexer.inc_line_no();
            }
            Rule::WhiteSpace => { // <Expr> (?:[ \t])+
            }
            Rule::Error => {
                // <*> .
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Error,
                    line_no: lexer.line_no(),
                    value: TokenValue::None,
                });
            }
            Rule::End => {
                if lexer.mode() == Mode::Expr {
                    lexer.yield_token(CalcToken {
                        token_id: TokenID::End,
                        line_no: lexer.line_no(),
                        value: TokenValue::None,
                    });
                } else {
                    lexer.yield_token(CalcToken {
                        token_id: TokenID::Error,
                        line_no: lexer.line_no(),
                        value: TokenValue::None,
                    });
                }
            }
        }
        Ok(())
    }
}

/// The calculator lexer.
///
/// `CalcLexer<I>` adapts a byte-oriented input stream `I` (that supports
/// contextual access to a [`SymTab`]) into an iterator-like interface that
/// yields [`CalcToken`]s. Internally, it owns a lower-level [`Lexer`] driven by
/// [`CalcLexerDriver`], which handles rule actions (e.g., interning identifiers,
/// parsing numbers, skipping comments/whitespace).
///
/// The generic parameter `I` must implement
/// [`TryNextWithContext<Item = u8, Context = SymTab>`], allowing the lexer to
/// pull bytes and mutate/read the external symbol table while tokenizing.
///
/// # Output
///
/// Each successful step returns a [`CalcToken`], containing:
/// - the token kind ([`TokenID`]),
/// - optional associated value ([`TokenValue`], e.g., `Ident` index or `Number`),
/// - and the source line (`line_no`) for diagnostics.
///
/// # Errors
///
/// Methods return a [`LexerError<I::Error, CalcError>`], where:
/// - `I::Error` is any error produced by the underlying input,
/// - [`CalcError`] covers lexical/parsing/UTF-8/symbol-table errors.
///
/// # Example
///
/// ```rust
/// # use parlex_calc::{CalcToken, CalcLexer, IterInput, SymTab, TokenID, TokenValue};
/// # use try_next::TryNextWithContext;
/// let mut symtab = SymTab::new();
/// let input = IterInput::from("hello\n +\n world\n\n123".bytes());
/// let mut lexer = CalcLexer::try_new(input).unwrap();
/// let vs = lexer.try_collect_with_context(&mut symtab).unwrap();
/// assert_eq!(vs.len(), 5);
/// assert_eq!(symtab.len(), 2);
/// ```
pub struct CalcLexer<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    /// The underlying DFA/engine that drives tokenization, parameterized by the
    /// input `I` and the driver that executes rule actions.
    lexer: Lexer<I, CalcLexerDriver<I>>,
}

impl<I> CalcLexer<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    /// Constructs a new calculator lexer over the provided input stream.
    ///
    /// This initializes an internal [`Lexer`] with a [`CalcLexerDriver`] that
    /// performs rule actions such as:
    /// - interning identifiers into the provided [`SymTab`] (via context),
    /// - converting matched byte slices into numbers/idents,
    /// - tracking line numbers and comment nesting.
    ///
    /// # Errors
    ///
    /// Returns a [`LexerError`] if the lexer cannot be constructed from the
    /// given input (rare, but may occur if the input source fails during setup).
    pub fn try_new(
        input: I,
    ) -> Result<
        Self,
        LexerError<<I as TryNextWithContext>::Error, <CalcLexerDriver<I> as LexerDriver>::Error>,
    > {
        let driver = CalcLexerDriver {
            comment_level: 0,
            _marker: PhantomData,
        };
        let lexer = Lexer::try_new(input, driver)?;
        Ok(Self { lexer })
    }
}
impl<I> TryNextWithContext for CalcLexer<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    /// Tokens produced by this lexer.
    type Item = CalcToken;

    /// Unified error type.
    type Error =
        LexerError<<I as TryNextWithContext>::Error, <CalcLexerDriver<I> as LexerDriver>::Error>;

    /// External context available while lexing (a [`SymTab`]).
    type Context = I::Context;

    /// Advances the lexer and returns the next token, or `None` at end of input.
    ///
    /// The provided `context` (typically a [`SymTab`]) may be mutated by rule
    /// actions (for example, to intern identifiers). This method is fallible;
    /// both input and lexical errors are converted into [`Self::Error`].
    ///
    /// # End of Input
    ///
    /// When the lexer reaches the end of the input stream, it will typically
    /// emit a final [`TokenID::End`] token before returning `None`.
    ///
    /// This explicit *End* token is expected by the **Parlex parser** to
    /// signal successful termination of a complete parsing unit.
    /// Consumers should treat this token as a logical *end-of-sentence* or
    /// *end-of-expression* marker, depending on the grammar.
    ///
    /// If the input contains **multiple independent sentences or expressions**,
    /// the lexer may emit multiple `End` tokens—one after each completed unit.
    /// In such cases, the parser can restart or resume parsing after each `End`
    /// to produce multiple parse results from a single input stream.
    ///
    /// Once all input has been consumed, the lexer returns `None`.
    fn try_next_with_context(
        &mut self,
        context: &mut I::Context,
    ) -> Result<Option<CalcToken>, <Self as TryNextWithContext>::Error> {
        self.lexer.try_next_with_context(context)
    }
}

/// A driver that defines semantic actions for the calculator parser.
///
/// The [`CalcParserDriver`] type implements [`ParserDriver`] and acts as the
/// bridge between the parser engine ([`Parser`]) and calculator-specific
/// semantic logic.
///
/// It provides the behavior for grammar reductions and ambiguity resolution
/// during parsing. Each reduction corresponds to a grammar production rule
/// in [`ParData`], and is responsible for building or evaluating partial
/// results (e.g., computing arithmetic expressions, populating the symbol
/// table), constructing AST, etc.
///
/// # Type Parameters
///
/// - `I`: The input source (the lexer) that yields [`CalcToken`]s and maintains a
///   contextual [`SymTab`]. Must implement
///   [`TryNextWithContext<Item = CalcToken, Context = SymTab>`].
///
/// # Associated Types
///
/// - `ParserData = ParData`:
///   Generated parser metadata containing grammar rules, production IDs,
///   and ambiguity identifiers.
/// - `Token = CalcToken`:
///   The token type produced by the lexer and consumed by this parser.
/// - `Parser = Parser<I, Self>`:
///   The parser engine parameterized by this driver.
/// - `Error = CalcError`:
///   Unified error type propagated during parsing.
/// - `Context = I::Context`:
///   Externally supplied context, such as a [`SymTab`].
///
/// # Responsibilities
///
/// The parser driver performs calculator-specific actions:
///
/// - **`resolve_ambiguity`** — invoked when the grammar allows multiple valid
///   interpretations of a token sequence. The driver chooses which parse path
///   to follow by returning an appropriate [`ParserAction`].
/// - **`reduce`** — executed when a grammar production completes. The driver
///   can perform semantic actions such as arithmetic evaluation, updating the
///   symbol table, or producing intermediate values.
///
/// # Example
/// ```rust,ignore
/// let mut driver = CalcParserDriver::<MyLexer>::default();
/// let mut parser = Parser::<MyLexer, _>::new(lexer, driver);
///
/// let mut symtab = SymTab::new();
/// while let Some(result) = parser.try_next_with_context(&mut symtab)? {
///     println!("Parsed expression result: {result:?}");
/// }
/// ```
///
/// # Notes
///
/// - The driver may be stateless (`_marker` only), or store intermediate
///   evaluation state if needed.
/// - Ambiguities can be resolved dynamically based on the current parse state
///   or the next lookahead token.
/// - The `reduce` method corresponds to grammar rules such as:
///   ```text
///   Expr → Expr '+' Term
///   Expr → Term
///   Term → NUMBER
///   ```
///   allowing the driver to fold numerical operations or emit results or
///   result  nodes.
pub struct CalcParserDriver<I> {
    /// Marker to associate the driver with its input type `I`.
    _marker: PhantomData<I>,
}

impl<I> ParserDriver for CalcParserDriver<I>
where
    I: TryNextWithContext<Item = CalcToken, Context = SymTab>,
{
    /// Parser metadata generated from the calculator grammar.
    type ParserData = ParData;

    /// Token type consumed by the parser.
    type Token = CalcToken;

    /// Concrete parser engine type.
    type Parser = Parser<I, Self>;

    /// Error type for semantic or parsing failures.
    type Error = CalcError;

    /// Context (symbol table or shared state).
    type Context = I::Context;

    /// Resolves grammar ambiguities when multiple parse actions are valid.
    ///
    /// The driver can inspect the parser conflict (`ambig`) and the upcoming
    /// token (`_tok2`) to decide which parse branch to follow. This method
    /// returns the selected [`ParserAction`].
    ///
    /// By default, most calculator grammars are unambiguous, so this method
    /// may simply return a default action or be left unimplemented.
    ///
    /// # Shift/Reduce Conflicts
    ///
    /// In practice, this hook is primarily used to resolve **Shift/Reduce**
    /// conflicts — cases where the parser can either:
    /// - **Reduce** using a completed production rule, or
    /// - **Shift** the next incoming token (`tok2`).
    ///
    /// Other types of conflicts (such as **Reduce/Reduce**) are much more
    /// difficult to handle programmatically and usually require modifying
    /// the grammar itself to eliminate ambiguity.
    ///
    /// In a typical arithmetic grammar, you can use operator precedence and
    /// associativity to decide whether to shift or reduce. For example:
    ///
    /// ```text
    /// Expr -> Expr '+' Expr
    /// ```
    ///
    /// When the incoming token is `*`, the driver can compare the precedence
    /// of `'+'` (lower) vs. `'*'` (higher) and decide to **Shift**, allowing
    /// the parser to defer reduction until the higher-precedence operation
    /// (`*`) is parsed first.
    ///
    /// This strategy ensures that the resulting parse tree respects the
    /// intended operator precedence and associativity rules.
    fn resolve_ambiguity(
        &mut self,
        _parser: &mut Self::Parser,
        _context: &mut Self::Context,
        ambig: <Self::ParserData as ParserData>::AmbigID,
        _tok2: &Self::Token,
    ) -> Result<ParserAction<StateID, ProdID, AmbigID>, Self::Error> {
        Ok(ParData::lookup_ambig(ambig)[1]) // Reduce
    }

    /// Performs semantic reduction for a completed grammar production.
    ///
    /// This is the main hook for calculator logic: each time the parser
    /// recognizes a rule (identified by `prod_id`), the driver can evaluate
    /// or construct the corresponding result, possibly updating the context.
    ///
    /// For example, when reducing:
    /// ```text
    /// Expr -> Expr '+' Expr
    /// ```
    /// the driver may pop the right-hand values from the parser stack, perform
    /// addition, and push the result back.
    fn reduce(
        &mut self,
        parser: &mut Self::Parser,
        context: &mut Self::Context,
        prod_id: <Self::ParserData as ParserData>::ProdID,
        token: &Self::Token,
    ) -> Result<(), Self::Error> {
        match prod_id {
            ProdID::Start => {
                // Start -> Seq
                // Accept - does not get reduced
                unreachable!()
            }
            ProdID::Stat1 => {
                // Stat ->
                parser.tokens_push(CalcToken {
                    token_id: TokenID::Stat,
                    line_no: token.line_no(),
                    value: TokenValue::None,
                });
            }
            ProdID::Stat2 => {
                // Stat -> Expr
                let mut expr = parser.tokens_pop();
                expr.token_id = TokenID::Stat;
                parser.tokens_push(expr);
            }
            ProdID::Stat3 => {
                // Stat -> ident = Expr
                let mut expr = parser.tokens_pop();
                let TokenValue::Number(value) = expr.value else {
                    unreachable!()
                };
                parser.tokens_pop();
                let ident = parser.tokens_pop();
                let TokenValue::Ident(index) = ident.value else {
                    unreachable!()
                };
                context.set(index, value)?;
                expr.token_id = TokenID::Stat;
                parser.tokens_push(expr);
            }
            ProdID::Expr1 => {
                // Expr -> number
                let mut number = parser.tokens_pop();
                number.token_id = TokenID::Expr;
                parser.tokens_push(number);
            }
            ProdID::Expr2 => {
                // Expr -> ident
                let mut tok = parser.tokens_pop();
                tok.token_id = TokenID::Expr;
                let TokenValue::Ident(index) = tok.value else {
                    unreachable!()
                };
                tok.value = TokenValue::Number(context.get(index)?);
                parser.tokens_push(tok);
            }
            ProdID::Expr3 => {
                // Expr -> Expr + Expr
                let expr2 = parser.tokens_pop();
                parser.tokens_pop();
                let mut expr1 = parser.tokens_pop();
                let TokenValue::Number(value1) = expr1.value else {
                    unreachable!()
                };
                let TokenValue::Number(value2) = expr2.value else {
                    unreachable!()
                };
                expr1.value = TokenValue::Number(value1 + value2);
                parser.tokens_push(expr1);
            }
            ProdID::Expr4 => {
                // Expr -> Expr - Expr
                let expr2 = parser.tokens_pop();
                parser.tokens_pop();
                let mut expr1 = parser.tokens_pop();
                let TokenValue::Number(value1) = expr1.value else {
                    unreachable!()
                };
                let TokenValue::Number(value2) = expr2.value else {
                    unreachable!()
                };
                expr1.value = TokenValue::Number(value1 - value2);
                parser.tokens_push(expr1);
            }
            ProdID::Expr5 => {
                // Expr -> Expr * Expr
                let expr2 = parser.tokens_pop();
                parser.tokens_pop();
                let mut expr1 = parser.tokens_pop();
                let TokenValue::Number(value1) = expr1.value else {
                    unreachable!()
                };
                let TokenValue::Number(value2) = expr2.value else {
                    unreachable!()
                };
                expr1.value = TokenValue::Number(value1 * value2);
                parser.tokens_push(expr1);
            }
            ProdID::Expr6 => {
                // Expr -> Expr / Expr
                let expr2 = parser.tokens_pop();
                parser.tokens_pop();
                let mut expr1 = parser.tokens_pop();
                let TokenValue::Number(value1) = expr1.value else {
                    unreachable!()
                };
                let TokenValue::Number(value2) = expr2.value else {
                    unreachable!()
                };
                expr1.value = TokenValue::Number(value1 / value2);
                parser.tokens_push(expr1);
            }
            ProdID::Expr7 => {
                // Expr -> - Expr
                let mut expr = parser.tokens_pop();
                parser.tokens_pop();
                let TokenValue::Number(value) = expr.value else {
                    unreachable!()
                };
                expr.value = TokenValue::Number(-value);
                parser.tokens_push(expr);
            }
            ProdID::Expr8 => {
                // Expr -> ( Expr )
                parser.tokens_pop();
                let expr = parser.tokens_pop();
                parser.tokens_pop();
                parser.tokens_push(expr);
            }
        }
        Ok(())
    }
}

/// The calculator parser, a wrapper that couples:
/// - the calculator lexer ([`CalcLexer`]) producing [`CalcToken`]s, and
/// - the calculator parser driver ([`CalcParserDriver`]) implementing reductions
///   and ambiguity resolution for the calculator grammar.
///
/// `CalcParser<I>` exposes an iterator-like interface via
/// [`TryNextWithContext`], yielding completed parse results (e.g., one per
/// “sentence” or top-level expression) while using a shared [`SymTab`] as
/// context. Internally it owns a generic [`Parser`] that pulls tokens
/// from `CalcLexer` and executes semantic actions in `CalcParserDriver`.
///
/// # Input / Output
///
/// - **Input**: any byte stream `I` implementing
///   [`TryNextWithContext<Item = u8, Context = SymTab>`].
/// - **Output**: completed parsing units as [`CalcToken`] values (typically
///   grammar-level results like expressions/statements).
///
/// # End Tokens and Multiple Sentences
///
/// The underlying lexer typically emits an explicit [`TokenID::End`] token at
/// the end of a *parsing unit* (end of “sentence” or expression). The parser
/// uses this to finalize and emit one result. If the input contains multiple
/// independent sentences, you will receive multiple results — one per `End` —
/// and `None` only after all input is consumed.
///
/// # Empty Statements
///
/// The calculator grammar also accepts an *empty* statement, which is returned
/// as a token with [`TokenValue::None`].
/// This occurs, for example, when the last statement in the input is terminated
/// by a semicolon (`;`) but followed by no further expression. In that case:
///
/// 1. The parser first emits the token for the preceding completed statement.
/// 2. It then emits an additional token representing the empty statement
///    (`TokenValue::None`).
/// 3. Finally, it returns `None`, indicating the end of the input stream.
///
/// This design allows the parser to fully reflect the structure of the input,
/// including empty or separator-only statements.
///
/// # Errors
///
/// All failures are surfaced through a composed
/// [`ParserError<LexerError<I::Error, CalcError>, CalcError, CalcToken>`]:
/// - `I::Error` — errors from the input source,
/// - [`CalcError`] — lexical/semantic errors (e.g., UTF-8, integer parsing,
///   symbol-table issues).
///
/// # Example
///
/// ```rust
/// # use parlex_calc::{CalcToken, CalcParser, IterInput, SymTab, TokenID, TokenValue};
/// # use try_next::TryNextWithContext;
/// let mut symtab = SymTab::new();
/// let input = IterInput::from("hello = 1;\n foo =\n 5 + 3 * 2;\n (world + hello + 10) * -2;\n\n1000 - - -123".bytes());
/// let mut parser = CalcParser::try_new(input).unwrap();
/// let vs = parser.try_collect_with_context(&mut symtab).unwrap();
/// assert_eq!(vs.len(), 4);
/// assert_eq!(symtab.len(), 3);
/// ```

/// # Example
///
/// ```rust
/// # use parlex_calc::{CalcToken, CalcParser, IterInput, SymTab, TokenID, TokenValue};
/// # use try_next::TryNextWithContext;
/// let mut symtab = SymTab::new();
/// let input = IterInput::from("hello = 1;\n 1 + 2;\n (world + hello + 10) * -2;\n\n1000 - - -123".bytes());
/// let mut parser = CalcParser::try_new(input).unwrap();
/// let vs = parser.try_collect_with_context(&mut symtab).unwrap();
/// assert_eq!(vs.len(), 4);
/// ```
pub struct CalcParser<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    parser: Parser<CalcLexer<I>, CalcParserDriver<CalcLexer<I>>>,
}

impl<I> CalcParser<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    pub fn try_new(
        input: I,
    ) -> Result<
        Self,
        ParserError<
            LexerError<
                <I as TryNextWithContext>::Error,
                <CalcLexerDriver<I> as LexerDriver>::Error,
            >,
            <CalcParserDriver<CalcLexer<I>> as ParserDriver>::Error,
            CalcToken,
        >,
    > {
        let lexer = CalcLexer::try_new(input).map_err(ParserError::Lexer)?;
        let driver = CalcParserDriver {
            _marker: PhantomData,
        };
        let parser = Parser::new(lexer, driver);
        Ok(Self { parser })
    }
}
impl<I> TryNextWithContext for CalcParser<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    type Item = CalcToken;
    type Error = ParserError<
        LexerError<<I as TryNextWithContext>::Error, <CalcLexerDriver<I> as LexerDriver>::Error>,
        <CalcParserDriver<CalcLexer<I>> as ParserDriver>::Error,
        CalcToken,
    >;
    type Context = I::Context;

    fn try_next_with_context(
        &mut self,
        context: &mut I::Context,
    ) -> Result<Option<CalcToken>, <Self as TryNextWithContext>::Error> {
        self.parser.try_next_with_context(context)
    }
}

#[cfg(test)]
mod tests {
    use crate::{CalcLexer, CalcParser, CalcToken, IterInput, SymTab, TokenID, TokenValue};
    use try_next::TryNextWithContext;

    #[test]
    fn calc_lexer_1() {
        let _ = env_logger::builder().is_test(true).try_init();
        let mut symtab = SymTab::new();
        let input = IterInput::from("hello\n +\n world\n\n123".bytes());
        let mut lexer = CalcLexer::try_new(input).unwrap();
        assert!(matches!(
            lexer.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Ident,
                line_no: 1,
                value: TokenValue::Ident(0)
            }),
        ));
        assert!(matches!(
            lexer.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Plus,
                line_no: 2,
                value: TokenValue::None
            }),
        ));
        assert!(matches!(
            lexer.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Ident,
                line_no: 3,
                value: TokenValue::Ident(1)
            }),
        ));
        assert!(matches!(
            lexer.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Number,
                line_no: 5,
                value: TokenValue::Number(123)
            }),
        ));
        assert!(matches!(
            lexer.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::End,
                line_no: 5,
                value: TokenValue::None
            }),
        ));
        assert!(matches!(
            lexer.try_next_with_context(&mut symtab).unwrap(),
            None,
        ));
    }

    #[test]
    fn calc_parser_1() {
        let _ = env_logger::builder().is_test(true).try_init();
        let mut symtab = SymTab::new();
        let input = IterInput::from(
            "hello = 1;\n 1 + 2;\n (world + hello + 10) * -2;\n\n1000 - - -123;".bytes(),
        );
        let mut parser = CalcParser::try_new(input).unwrap();
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                line_no: 1,
                value: TokenValue::Number(1)
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                line_no: 2,
                value: TokenValue::Number(3)
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                line_no: 3,
                value: TokenValue::Number(-22)
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                line_no: 5,
                value: TokenValue::Number(877)
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                line_no: 5,
                value: TokenValue::None
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            None,
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            None,
        ));
    }
}
