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

use lexer_data::{LexData, Mode, Rule};
use parlex::{
    Lexer, LexerData, LexerDriver, LexerError, Parser, ParserAction, ParserData, ParserDriver,
    ParserError, Token,
};
use parser_data::{AmbigID, ParData, ProdID, StateID, TokenID};
use smartstring::alias::String;
use std::collections::HashMap;
use thiserror::Error;
use try_next::TryNextWithContext;

#[derive(Debug, Error)]
pub enum CalcError {
    /// Encountered an invalid or unexpected byte.
    #[error("unable to parse {0:?}")]
    ParseIntError(#[from] std::num::ParseIntError),

    /// Failed to decode UTF-8 from input.
    #[error("utf8 error {0:?}")]
    FromUtf8(#[from] std::string::FromUtf8Error),
}

pub struct ByteInput<'a> {
    slice: &'a [u8],
}
impl<'a> ByteInput<'a> {
    pub fn from(bytes: &'a [u8]) -> Self {
        Self { slice: bytes }
    }
}
impl<'a> TryNextWithContext for ByteInput<'a> {
    type Item = u8;
    type Error = std::convert::Infallible;
    type Context = SymTab;

    #[inline]
    fn try_next_with_context(
        &mut self,
        _context: &mut Self::Context,
    ) -> Result<Option<Self::Item>, Self::Error> {
        match self.slice.split_first() {
            Some((b, rest)) => {
                self.slice = rest;
                Ok(Some(*b))
            }
            None => Ok(None),
        }
    }
}

/// A simple symbol table mapping string names to 64-bit unsigned integer values.
///
/// This can be used, for example, in assemblers, interpreters, or compilers
/// to associate identifiers (symbols) with addresses or constants.
///
/// # Examples
/// ```rust
/// # use parlex_calc::SymTab;
/// let mut symtab = SymTab::new();
/// symtab.set("x", 42);
/// assert_eq!(symtab.get("x"), 42);
/// assert_eq!(symtab.get("y"), 0); // undefined symbol returns 0
/// ```
pub struct SymTab {
    tab: HashMap<String, i64>,
}

impl SymTab {
    /// Creates a new, empty symbol table.
    pub fn new() -> Self {
        Self {
            tab: HashMap::new(),
        }
    }

    /// Inserts or updates the value of a symbol in the table.
    ///
    /// If the symbol already exists, its value is overwritten.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the symbol to set.
    /// * `value` - The numeric value associated with the symbol.
    ///
    /// # Example
    /// ```rust
    /// # use parlex_calc::SymTab;
    /// let mut symtab = SymTab::new();
    /// symtab.set("counter", 100);
    /// assert_eq!(symtab.get("counter"), 100);
    /// ```
    pub fn set(&mut self, name: impl AsRef<str>, value: i64) {
        self.tab.insert(String::from(name.as_ref()), value);
    }

    /// Retrieves the value of a symbol, returning `0` if undefined.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the symbol to look up.
    ///
    /// # Returns
    ///
    /// * The symbol's associated value, or `0` if not found.
    ///
    /// # Example
    /// ```rust
    /// # use parlex_calc::SymTab;
    /// let mut symtab = SymTab::new();
    /// symtab.set("flag", 1);
    /// assert_eq!(symtab.get("flag"), 1);
    /// assert_eq!(symtab.get("missing"), 0);
    /// ```
    pub fn get(&self, name: impl AsRef<str>) -> i64 {
        *self.tab.get(name.as_ref()).unwrap_or(&0)
    }
}

/// 1. Define token
#[derive(Debug, Clone)]
pub enum TokenValue {
    None,
    Ident(String),
    Number(i64),
}

#[derive(Debug, Clone)]
pub struct CalcToken {
    pub token_id: TokenID,
    pub line_no: usize,
    pub value: TokenValue,
}

impl Token for CalcToken {
    type TokenID = TokenID;

    fn token_id(&self) -> Self::TokenID {
        self.token_id
    }
    fn line_no(&self) -> usize {
        self.line_no
    }
}

/// 2. define lexer driver
pub struct CalcLexerDriver<I> {
    comment_level: i32,
    _marker: std::marker::PhantomData<I>,
}

impl<I> LexerDriver for CalcLexerDriver<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    type LexerData = LexData;
    type Token = CalcToken;
    type Lexer = Lexer<I, Self>;
    type Error = CalcError;
    type Context = I::Context;

    fn action(
        &mut self,
        lexer: &mut Self::Lexer,
        _context: &mut Self::Context,
        rule: <Self::LexerData as LexerData>::LexerRule,
    ) -> Result<(), Self::Error> {
        match rule {
            Rule::Empty => {
                unreachable!()
            }
            Rule::Ident => {
                // <Expr> (?:[a-z_][a-z_A-Z0-9]*)
                let s = lexer.take_str()?;
                lexer.yield_token(CalcToken {
                    token_id: TokenID::Ident,
                    line_no: lexer.line_no(),
                    value: TokenValue::Ident(s),
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

/// 3. define lexer
///
/// # Example
///
/// ```rust
/// # use parlex_calc::{CalcToken, CalcLexer, ByteInput, SymTab, TokenID, TokenValue};
/// # use try_next::TryNextWithContext;
/// let mut symtab = SymTab::new();
/// let input = ByteInput::from(b"hello\n +\n world\n\n123");
/// let mut lexer = CalcLexer::try_new(input).unwrap();
/// dbg!(lexer.try_next_with_context(&mut symtab).unwrap());
/// ```
pub struct CalcLexer<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    lexer: Lexer<I, CalcLexerDriver<I>>,
}

impl<I> CalcLexer<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    pub fn try_new(
        input: I,
    ) -> Result<
        Self,
        LexerError<<I as TryNextWithContext>::Error, <CalcLexerDriver<I> as LexerDriver>::Error>,
    > {
        let driver = CalcLexerDriver {
            comment_level: 0,
            _marker: std::marker::PhantomData,
        };
        let lexer = Lexer::try_new(input, driver)?;
        Ok(Self { lexer })
    }
}
impl<I> TryNextWithContext for CalcLexer<I>
where
    I: TryNextWithContext<Item = u8, Context = SymTab>,
{
    type Item = CalcToken;
    type Error =
        LexerError<<I as TryNextWithContext>::Error, <CalcLexerDriver<I> as LexerDriver>::Error>;
    type Context = I::Context;

    fn try_next_with_context(
        &mut self,
        context: &mut I::Context,
    ) -> Result<Option<CalcToken>, <Self as TryNextWithContext>::Error> {
        self.lexer.try_next_with_context(context)
    }
}

/// 4. Define parser driver
pub struct CalcParserDriver<I> {
    _marker: std::marker::PhantomData<I>,
}

impl<I> ParserDriver for CalcParserDriver<I>
where
    I: TryNextWithContext<Item = CalcToken, Context = SymTab>,
{
    type ParserData = ParData;
    type Token = CalcToken;
    type Parser = Parser<I, Self>;
    type Error = CalcError;
    type Context = I::Context;

    fn resolve_ambiguity(
        &mut self,
        _parser: &mut Self::Parser,
        _context: &mut Self::Context,
        ambig: <Self::ParserData as ParserData>::AmbigID,
        _tok2: &Self::Token,
    ) -> Result<ParserAction<StateID, ProdID, AmbigID>, Self::Error> {
        Ok(ParData::lookup_ambig(ambig)[1])
    }

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
                parser.tokens_pop();
                let ident = parser.tokens_pop();
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
                let mut ident = parser.tokens_pop();
                ident.token_id = TokenID::Expr;
                let TokenValue::Ident(name) = ident.value else {
                    unreachable!()
                };
                ident.value = TokenValue::Number(context.get(name));
                parser.tokens_push(ident);
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

/// 5. Define parser
/// # Example
///     
/// ```rust
/// # use parlex_calc::{CalcToken, CalcParser, ByteInput, SymTab, TokenID, TokenValue};
/// # use try_next::TryNextWithContext;
/// let mut symtab = SymTab::new();
/// let input = ByteInput::from(b"hello = 1;\n 1 + 2;\n (world + hello + 10) * -2;\n\n1000 - - -123");
/// let mut parser = CalcParser::try_new(input).unwrap();
/// dbg!(parser.try_next_with_context(&mut symtab).unwrap());
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
            _marker: std::marker::PhantomData,
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
    use crate::{ByteInput, CalcLexer, CalcParser, CalcToken, SymTab, TokenID, TokenValue};
    use try_next::TryNextWithContext;

    #[test]
    fn calc_lexer_1() {
        let _ = env_logger::builder().is_test(true).try_init();
        let mut symtab = SymTab::new();
        let input = ByteInput::from(b"hello\n +\n world\n\n123");
        let mut lexer = CalcLexer::try_new(input).unwrap();
        assert!(matches!(
            lexer.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken { token_id: TokenID::Ident, line_no: 1, value: TokenValue::Ident(ref s) }) if s == "hello",
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
            Some(CalcToken { token_id: TokenID::Ident, line_no: 3, value: TokenValue::Ident(ref s) }) if s == "world",
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
        let input =
            ByteInput::from(b"hello = 1;\n 1 + 2;\n (world + hello + 10) * -2;\n\n1000 - - -123;");
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
                value: TokenValue::Number(-20)
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
