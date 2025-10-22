//! # Calculator Parser
//!
//! This module couples the generated SLR(1) parser tables with calculator-
//! specific semantic actions. It exposes:
//!
//! - [`parser_data`]: generated automaton, productions, and IDs,
//! - [`CalcParserDriver`]: semantic hooks for reductions and ambiguities,
//! - [`CalcParser`]: a thin adapter that pulls tokens from the lexer and
//!   yields fully reduced results.
//!
//! The parser consumes tokens produced by [`CalcLexer`] and uses a mutable
//! [`SymTab`] as shared context (for interning identifiers and storing values).
//!
//! ## Behavior highlights
//! - **Operator precedence & associativity** are enforced via the ambiguity
//!   resolver: **shift** on higher-precedence lookahead, otherwise **reduce**.
//!   All binary operators in this grammar are left-associative; the prefix
//!   unary minus is handled separately and does not introduce conflicts.
//! - **Assignments** store the value in the symbol table and evaluate to the
//!   assigned value.
//! - **Empty statements** (a bare `;`) are emitted as a `Stat` token with
//!   [`TokenValue::None`].

use crate::{CalcLexer, CalcToken, SymTab, TokenID, TokenValue};
use parlex::{
    LexerStats, ParlexError, Parser, ParserAction, ParserData, ParserDriver, ParserStats, Token,
};
use parser_data::{AmbigID, ParData, ProdID, StateID};
use std::marker::PhantomData;
use try_next::TryNextWithContext;

/// Includes the generated SLR parser tables and definitions.
///
/// This file (`parser_data.rs`) is produced by the **parlex-gen** [`aslr`] tool
/// during the build process. It defines the parsing automaton, rule metadata,
/// and associated enum types used by the [`CalcParser`].
pub mod parser_data {
    include!(concat!(env!("OUT_DIR"), "/parser_data.rs"));
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
///   [`TryNextWithContext<SymTab, Item = CalcToken>`].
///
/// # Associated Types
///
/// - `ParserData = ParData`:
///   Generated parser metadata containing grammar rules, production IDs,
///   and ambiguity identifiers.
/// - `Token = CalcToken`:
///   The token type produced by the lexer and consumed by this parser.
/// - `Parser = Parser<I, Self, SymTab>`:
///   The parser engine parameterized by this driver and context.
/// - `Error = CalcError`:
///   Unified error type propagated during parsing.
/// - `Context = SymTab`:
///   Externally supplied context.
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
/// # Notes
///
/// - The driver may be stateless (`_marker` only), or store intermediate
///   evaluation state if needed.
/// - Ambiguities can be resolved dynamically based on the current parse state
///   or the next lookahead token.
/// - The `reduce` method corresponds to grammar rules such as:
///   ```text
///   Expr → Expr '+' Expr
///   Expr → NUMBER
///   ```
///   allowing the driver to fold numerical operations or emit results or
///   result  nodes.
pub struct CalcParserDriver<I> {
    /// Marker to associate the driver with its input type `I`.
    _marker: PhantomData<I>,
}

impl<I> ParserDriver for CalcParserDriver<I>
where
    I: TryNextWithContext<
            SymTab,
            LexerStats,
            Item = CalcToken,
            Error: std::fmt::Display + 'static,
        >,
{
    /// Parser metadata generated from the calculator grammar.
    type ParserData = ParData;

    /// Token type consumed by the parser.
    type Token = CalcToken;

    /// Concrete parser engine type.
    type Parser = Parser<I, Self, Self::Context>;

    /// Context (symbol table or shared state).
    type Context = SymTab;

    /// Resolves grammar ambiguities when multiple parse actions are valid.
    ///
    /// The driver can inspect the parser conflict (`ambig`) and the upcoming
    /// token (`token`) to decide which parse branch to follow. This method
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
    /// - **Shift** the next incoming token (`token`).
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
        token: &Self::Token,
    ) -> Result<ParserAction<StateID, ProdID, AmbigID>, ParlexError> {
        let ambig_tab = ParData::lookup_ambig(ambig);
        let shift = ambig_tab[0];
        let reduce = ambig_tab[1];
        let ParserAction::Shift(_) = shift else {
            panic!("expected shift");
        };
        let ParserAction::Reduce(prod_id) = reduce else {
            panic!("expected reduce");
        };
        let CalcToken { token_id, .. } = token;

        match prod_id {
            ProdID::Expr3 | ProdID::Expr4 => {
                // Expr -> Expr + Expr | Expr - Expr
                match token_id {
                    TokenID::Plus | TokenID::Minus => Ok(reduce), // `+` and `-` are left-associative; `-` can't be unary in this context
                    TokenID::Asterisk | TokenID::Slash => Ok(shift), // `*` and `/` have higher precedence than `+` and `-`
                    _ => unreachable!(),
                }
            }
            ProdID::Expr5 | ProdID::Expr6 => {
                // Expr -> Expr * Expr | Expr / Expr
                Ok(reduce) // the lookahead `-` can't be unary; therefore, we reduce either by higher precedence or left associativity
            }
            ProdID::Expr7 => {
                // Expr -> - Expr
                Ok(reduce) // unary `-` has higher precedence than anything else
            }
            _ => panic!("unexpected prod in ambiguity"),
        }
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
    ) -> Result<(), ParlexError> {
        match prod_id {
            ProdID::Start => {
                // Start -> Stat
                // Accept - does not get reduced
                unreachable!()
            }
            ProdID::Stat1 => {
                // Stat ->
                parser.tokens_push(CalcToken {
                    token_id: TokenID::Stat,
                    span: token.span(),
                    value: TokenValue::None,
                });
            }
            ProdID::Stat2 => {
                // Stat -> comment Stat
                let mut stat = parser.tokens_pop();
                let comment_tok = parser.tokens_pop();
                let TokenValue::Comment(comment) = comment_tok.value else {
                    unreachable!()
                };
                stat.to_statement(Some(comment));
                stat.merge_span(&comment_tok.span);
                parser.tokens_push(stat);
            }
            ProdID::Stat3 => {
                // Stat -> Expr
                let mut expr = parser.tokens_pop();
                expr.token_id = TokenID::Stat;
                parser.tokens_push(expr);
            }
            ProdID::Stat4 => {
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
                context
                    .set(index, value)
                    .map_err(|e| ParlexError::from_err(e, ident.span()))?; //TODO: fix span
                expr.token_id = TokenID::Stat;
                expr.merge_span(&ident.span);
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
                tok.value = TokenValue::Number(
                    context
                        .get(index)
                        .map_err(|e| ParlexError::from_err(e, tok.span()))?,
                );
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
                expr1.merge_span(&expr2.span);
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
                expr1.merge_span(&expr2.span);
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
                expr1.merge_span(&expr2.span);
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
                expr1.merge_span(&expr2.span);
                parser.tokens_push(expr1);
            }
            ProdID::Expr7 => {
                // Expr -> - Expr
                let mut expr = parser.tokens_pop();
                let minus = parser.tokens_pop();
                let TokenValue::Number(value) = expr.value else {
                    unreachable!()
                };
                expr.value = TokenValue::Number(-value);
                expr.merge_span(&minus.span);
                parser.tokens_push(expr);
            }
            ProdID::Expr8 => {
                // Expr -> ( Expr )
                let left_paren = parser.tokens_pop();
                let mut expr = parser.tokens_pop();
                let right_paren = parser.tokens_pop();
                expr.merge_span(&left_paren.span);
                expr.merge_span(&right_paren.span);
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
///   [`TryNextWithContext<SymTab, Item = u8>`].
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
/// # use parlex_calc::{CalcToken, CalcParser, SymTab, TokenID, TokenValue};
/// # use try_next::{IterInput, TryNextWithContext};
/// let mut symtab = SymTab::new();
/// let input = IterInput::from("hello = 1;\n foo =\n 5 + 3 * 2;\n (world + hello + 10) * -2;\n\n1000 - - -123".bytes());
/// let mut parser = CalcParser::try_new(input).unwrap();
/// let vs = parser.try_collect_with_context(&mut symtab).unwrap();
/// assert_eq!(vs.len(), 4);
/// assert_eq!(symtab.len(), 3);
/// ```
pub struct CalcParser<I>
where
    I: TryNextWithContext<SymTab, Item = u8, Error: std::fmt::Display + 'static>,
{
    parser: Parser<CalcLexer<I>, CalcParserDriver<CalcLexer<I>>, SymTab>,
}

impl<I> CalcParser<I>
where
    I: TryNextWithContext<SymTab, Item = u8, Error: std::fmt::Display + 'static>,
{
    pub fn try_new(input: I) -> Result<Self, ParlexError> {
        let lexer = CalcLexer::try_new(input)?;
        let driver = CalcParserDriver {
            _marker: PhantomData,
        };
        let parser = Parser::new(lexer, driver);
        Ok(Self { parser })
    }
}
impl<I> TryNextWithContext<SymTab, (LexerStats, ParserStats)> for CalcParser<I>
where
    I: TryNextWithContext<SymTab, Item = u8, Error: std::fmt::Display + 'static>,
{
    type Item = CalcToken;
    type Error = ParlexError;

    /// Returns the next fully reduced unit (`Stat`), or `None` at end of input.
    ///
    /// The underlying lexer typically emits an explicit [`TokenID::End`] at
    /// unit boundaries (e.g., semicolon-terminated statements). The parser
    /// finalizes and yields one `Stat` per such boundary.
    fn try_next_with_context(
        &mut self,
        context: &mut SymTab,
    ) -> Result<Option<CalcToken>, ParlexError> {
        self.parser.try_next_with_context(context)
    }

    fn stats(&self) -> (LexerStats, ParserStats) {
        self.parser.stats()
    }
}

#[cfg(test)]
mod tests {
    use crate::{CalcParser, CalcToken, SymTab, TokenID, TokenValue};
    use parlex::span;
    use try_next::{IterInput, TryNextWithContext};

    #[test]
    fn parses_four_stats() {
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
                span: span!(0, 0, 0, 9),
                value: TokenValue::Number(1)
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                span: span!(1, 1, 1, 6),
                value: TokenValue::Number(3)
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                span: span!(2, 1, 2, 26),
                value: TokenValue::Number(-22)
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                span: span!(4, 0, 4, 13),
                value: TokenValue::Number(877)
            }),
        ));
        assert!(matches!(
            parser.try_next_with_context(&mut symtab).unwrap(),
            Some(CalcToken {
                token_id: TokenID::Stat,
                span: span!(4, 14, 4, 14),
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

    #[test]
    fn parses_assignment_and_reference() {
        // x = 2; x + 3;
        let _ = env_logger::builder().is_test(true).try_init();
        let mut symtab = SymTab::new();
        let input = IterInput::from("x = 2;\n x + 3;".bytes());
        let mut parser = CalcParser::try_new(input).unwrap();

        // x = 2;
        let t1 = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        assert!(matches!(
            t1,
            CalcToken {
                token_id: TokenID::Stat,
                span: span!(0, 0, 0, 5),
                value: TokenValue::Number(2)
            }
        ));

        // x + 3;
        let t2 = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        assert!(matches!(
            t2,
            CalcToken {
                token_id: TokenID::Stat,
                span: span!(1, 1, 1, 6),
                value: TokenValue::Number(5)
            }
        ));

        // empty
        let t3 = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        assert!(matches!(
            t3,
            CalcToken {
                token_id: TokenID::Stat,
                span: span!(1, 7, 1, 7),
                value: TokenValue::None
            }
        ));

        // EOF
        assert!(parser.try_next_with_context(&mut symtab).unwrap().is_none());
        // symbol table contains one identifier
        assert_eq!(symtab.len(), 1);
    }

    #[test]
    fn respects_operator_precedence_and_unary_minus() {
        // 1 + 2 * 3;  -(1 + 2) * 3;
        let _ = env_logger::builder().is_test(true).try_init();
        let mut symtab = SymTab::new();
        let input = IterInput::from("1 + 2 * 3;\n-(1 + 2) * 3".bytes());
        let mut parser = CalcParser::try_new(input).unwrap();

        // 1 + 2 * 3 => 7
        let t1 = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        dbg!(parser.stats());
        assert!(matches!(
            t1,
            CalcToken {
                token_id: TokenID::Stat,
                span: span!(0, 0, 0, 9),
                value: TokenValue::Number(7)
            }
        ));

        // -(1 + 2) * 3 => -9
        let t2 = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        assert!(matches!(
            t2,
            CalcToken {
                token_id: TokenID::Stat,
                span: span!(1, 0, 1, 12),
                value: TokenValue::Number(-9)
            }
        ));

        assert!(parser.try_next_with_context(&mut symtab).unwrap().is_none());
    }

    #[test]
    fn emits_empty_statement_as_none() {
        // 1; ;
        let _ = env_logger::builder().is_test(true).try_init();
        let mut symtab = SymTab::new();
        let input = IterInput::from("1; ;".bytes());
        let mut parser = CalcParser::try_new(input).unwrap();

        // 1;
        let t1 = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        assert!(matches!(
            t1,
            CalcToken {
                token_id: TokenID::Stat,
                value: TokenValue::Number(1),
                ..
            }
        ));

        // empty ;
        let t2 = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        assert!(matches!(
            t2,
            CalcToken {
                token_id: TokenID::Stat,
                value: TokenValue::None,
                ..
            }
        ));

        // empty EOF
        let t3 = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        assert!(matches!(
            t3,
            CalcToken {
                token_id: TokenID::Stat,
                value: TokenValue::None,
                ..
            }
        ));

        // EOF
        assert!(parser.try_next_with_context(&mut symtab).unwrap().is_none());
    }

    #[test]
    fn parentheses_override_precedence() {
        // (1 + 2) * 3 => 9
        let _ = env_logger::builder().is_test(true).try_init();
        let mut symtab = SymTab::new();
        let input = IterInput::from("(1 + 2) * 3".bytes());
        let mut parser = CalcParser::try_new(input).unwrap();

        let t = parser.try_next_with_context(&mut symtab).unwrap().unwrap();
        assert!(matches!(
            t,
            CalcToken {
                token_id: TokenID::Stat,
                value: TokenValue::Number(9),
                ..
            }
        ));

        assert!(parser.try_next_with_context(&mut symtab).unwrap().is_none());
    }
}
