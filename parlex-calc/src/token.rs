//! # Calculator Tokens
//!
//! This module defines the concrete token value and token type used by the
//! calculator parser. It provides:
//!
//! - [`TokenValue`]: the payload carried by lexical tokens (e.g., symbol-table
//!   indices for identifiers or numeric literals),
//! - [`CalcToken`]: a concrete token implementation that pairs a [`TokenID`],
//!   a [`TokenValue`], and a source line number, and implements the core
//!   [`parlex::Token`] trait.
//!
//! These types are produced by the lexer and consumed by later stages of the
//! pipeline (e.g., the parser and semantic analysis).
use crate::TokenID;
use parlex::{Span, Token};
use smartstring::alias::String;

/// The payload carried by a lexical token.
///
/// Tokens may or may not carry extra data depending on their kind. For example,
/// identifiers and numbers store auxiliary information such as a symbol-table
/// index or a literal integer value.
///
/// This payload is paired with a [`TokenID`] inside a [`CalcToken`].
///
/// # Variants
///
/// - [`TokenValue::None`]:
///   No extra data (typical for punctuation or operators).
///
/// - [`TokenValue::Ident(usize)`]:
///   The **symbol table index** for an identifier. The `usize` refers to an
///   entry managed by the symbol table (see your crate’s `SymTab` type).
///
/// - [`TokenValue::Number(i64)`]:
///   A parsed integer literal.
///
/// # Example
/// ```rust
/// # use parlex_calc::TokenValue;
/// // Construct a token representing a number
/// let token = TokenValue::Number(42);
///
/// // Ensure that it is a number, and extract its value
/// let TokenValue::Number(n) = token else {
///     panic!("Expected a numeric token");
/// };
///
/// println!("Numeric literal: {n}");
/// assert_eq!(n, 42);
/// ```
#[derive(Debug, Clone)]
pub enum TokenValue {
    /// No associated data (for symbols or keywords).
    None,

    /// Identifier token with an index into the symbol table.
    Ident(usize),

    /// Integer literal token.
    Number(i64),

    /// Comment.
    Comment(String),
}

/// A concrete lexical token for the calculator frontend.
///
/// `CalcToken` is a lightweight container that implements [`parlex::Token`],
/// exposing its identifier and source position. It groups:
///
/// - a token kind via [`TokenID`],
/// - an optional payload via [`TokenValue`],
/// - a 1-based source line number.
///
/// # Trait implementation
///
/// Implements [`Token`] with:
/// - [`token_id`](Token::token_id): returns the token’s [`TokenID`],
/// - [`line_no`](Token::line_no): returns the token’s source line number.
///
/// # Fields
///
/// - [`token_id`](#structfield.token_id): the token’s category (identifier, number, operator, …)
/// - [`value`](#structfield.value): associated payload (symbol index or literal)
/// - [`line_no`](#structfield.line_no): 1-based source line number
///
/// # Example
/// ```rust
/// # use parlex_calc::{CalcToken, TokenID, TokenValue};
/// # use parlex::{Token, span};
/// let tok = CalcToken {
///     token_id: TokenID::Number,
///     value: TokenValue::Number(99),
///     span: span!(0, 0, 0, 2),
/// };
///
/// assert_eq!(tok.token_id(), TokenID::Number);
/// assert_eq!(tok.span(), span!(0, 0, 0, 2));
/// ```
#[derive(Debug, Clone)]
pub struct CalcToken {
    /// The token’s kind or category (e.g. identifier, operator, number).
    pub token_id: TokenID,
    /// The associated value for the token, if applicable.
    pub value: TokenValue,
    /// The line number in the input source where the token occurs.
    pub span: Option<Span>,
}

impl CalcToken {
    pub fn merge_span(&mut self, other_span: &Option<Span>) {
        match other_span {
            Some(other_span) => match &mut self.span {
                Some(my_span) => {
                    *my_span = my_span.merge(other_span);
                }
                None => {
                    self.span = Some(*other_span);
                }
            },
            None => (),
        }
    }
}

impl Token for CalcToken {
    /// The associated identifier type used to classify this token.
    type TokenID = TokenID;

    /// Returns the token’s kind identifier.
    fn token_id(&self) -> Self::TokenID {
        self.token_id
    }

    /// Returns the line number where the token appears.
    fn span(&self) -> Option<Span> {
        self.span
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parlex::{Position, span};

    #[test]
    fn token_value_number_extraction_with_let_else() {
        let tok = TokenValue::Number(42);

        // Ensure it's a number and extract the value
        let TokenValue::Number(n) = tok else {
            panic!("Expected a numeric token");
        };

        assert_eq!(n, 42);
    }

    #[test]
    #[should_panic(expected = "Expected a numeric token")]
    fn token_value_number_extraction_should_panic_if_not_number() {
        let tok = TokenValue::Ident(5);

        // This will panic due to pattern mismatch
        let TokenValue::Number(_n) = tok else {
            panic!("Expected a numeric token");
        };
    }

    #[test]
    fn token_value_ident_stores_symbol_index() {
        let idx = 7usize;
        let tok = TokenValue::Ident(idx);

        if let TokenValue::Ident(i) = tok {
            assert_eq!(i, idx);
        } else {
            panic!("Expected Ident token");
        }
    }

    #[test]
    fn token_value_none_matches() {
        let tok = TokenValue::None;
        assert!(matches!(tok, TokenValue::None));
    }

    #[test]
    fn calc_token_trait_accessors_return_values() {
        let t = CalcToken {
            token_id: TokenID::Number,
            value: TokenValue::Number(99),
            span: span!(1, 2, 1, 10),
        };

        assert_eq!(t.token_id(), TokenID::Number);
        assert_eq!(t.span().unwrap().start.column, 2);
    }

    #[test]
    fn calc_token_with_identifier_round_trip() {
        let t = CalcToken {
            token_id: TokenID::Ident,
            value: TokenValue::Ident(5),
            span: span!(1, 2, 1, 10),
        };

        assert_eq!(t.token_id(), TokenID::Ident);

        if let TokenValue::Ident(i) = t.value {
            assert_eq!(i, 5);
        } else {
            panic!("Expected TokenValue::Ident");
        }

        assert_eq!(t.span().unwrap().display(), "span 1:2 to 1:10");
    }

    #[test]
    fn calc_token_is_cloneable_and_debuggable() {
        let t1 = CalcToken {
            token_id: TokenID::Number,
            value: TokenValue::Number(-1),
            span: span!(10, 20, 12, 20),
        };

        let t2 = t1.clone();
        assert_eq!(t2.token_id(), t1.token_id());
        assert_eq!(t2.span().unwrap().display(), "span 10:20 to 12:20");

        let dbg_out = format!("{t1:?}");
        assert!(dbg_out.contains("CalcToken"));
    }

    #[test]
    #[should_panic(expected = "Expected TokenValue::Ident")]
    fn calc_token_with_identifier_should_panic_if_wrong_kind() {
        let t = CalcToken {
            token_id: TokenID::Number,
            value: TokenValue::Number(0),
            span: span!(10, 20, 12, 20),
        };

        if let TokenValue::Ident(_) = t.value {
            // should never reach
        } else {
            panic!("Expected TokenValue::Ident");
        }
    }

    fn sp(sl: usize, sc: usize, el: usize, ec: usize) -> Span {
        Span::new(Position::new(sl, sc), Position::new(el, ec))
    }

    fn tok(token_id: TokenID, value: TokenValue, span: Option<Span>) -> CalcToken {
        CalcToken {
            token_id,
            value,
            span,
        }
    }

    // 1) Existing span + other span => expand to cover both ends.
    #[test]
    fn merge_span_expands_existing_span_to_cover_both() {
        let mut t = tok(
            TokenID::Number,
            TokenValue::Number(1),
            Some(sp(0, 5, 0, 10)),
        );
        let other = Some(sp(0, 2, 0, 12));

        t.merge_span(&other);

        let m = t.span.unwrap();
        assert_eq!(m.start, Position::new(0, 2));
        assert_eq!(m.end, Position::new(0, 12));
    }

    // 2) self.span == None, other == Some(...) => set span.
    #[test]
    fn merge_span_sets_when_self_is_none() {
        let mut t = tok(TokenID::Ident, TokenValue::Ident(0), None);
        let new_span = Some(sp(1, 0, 1, 3));

        t.merge_span(&new_span);

        assert_eq!(t.span, new_span);
    }

    // 3) other == None => no-op (existing span preserved).
    #[test]
    fn merge_span_is_noop_when_other_is_none() {
        let before = Some(sp(2, 4, 2, 9));
        let mut t = tok(TokenID::Number, TokenValue::Number(0), before);

        t.merge_span(&None);

        assert_eq!(t.span, before);
    }

    // 4) self.span == None and other == None => remains None.
    #[test]
    fn merge_span_both_none_remains_none() {
        let mut t = tok(TokenID::Number, TokenValue::Number(0), None);

        t.merge_span(&None);

        assert!(t.span.is_none());
    }

    // 5) other fully inside self => merged span unchanged.
    #[test]
    fn merge_span_other_within_self_no_change() {
        let mut t = tok(
            TokenID::Number,
            TokenValue::Number(0),
            Some(sp(5, 2, 5, 10)),
        );
        let inner = Some(sp(5, 4, 5, 7)); // strictly inside

        t.merge_span(&inner);

        assert_eq!(t.span, Some(sp(5, 2, 5, 10)));
    }

    // 6) cross-line merge: expands across lines correctly.
    #[test]
    fn merge_span_cross_line_expands() {
        // self: [1:5 .. 2:3), other: [0:9 .. 3:1) => merged: [0:9 .. 3:1)
        let mut t = tok(TokenID::Ident, TokenValue::Ident(1), Some(sp(1, 5, 2, 3)));
        let other = Some(sp(0, 9, 3, 1));

        t.merge_span(&other);

        let m = t.span.unwrap();
        assert_eq!(m.start, Position::new(0, 9));
        assert_eq!(m.end, Position::new(3, 1));
    }
}
