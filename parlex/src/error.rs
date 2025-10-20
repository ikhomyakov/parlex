//! Core source-location and error types used in lexical and syntactic analysis.
//!
//! This module defines small types commonly used by lexers/parsers for
//! tracking source locations and reporting errors with spans. It also
//! provides a convenient `span!` macro for building `Option<Span>` values
//! inline (handy when populating error structs).
//!
//! # Examples
//!
//! ```rust
//! # use parlex::{ParlexError, Span, Position, span};
//! let start = Position::new(3, 5);
//! let end   = Position::new(3, 10);
//! let sp = Span::new(start, end);
//! assert_eq!(sp.is_empty(), false);
//! assert_eq!(sp.line_range(), (3, 3));
//!
//! let err = ParlexError {
//!     message: "unexpected token".into(),
//!     span: Some(sp),
//! };
//! assert!(err.to_string().contains("unexpected token"));
//!
//! // Build an Option<Span> with the macro
//! let sp_opt = span!(1, 1, 1, 5);
//! assert!(sp_opt.is_some());
//! ```

use thiserror::Error;

/// A 1-based line/column position in source text.
///
/// `line` and `column` are typically 1-based (human-facing). If you prefer
/// 0-based internally, convert in your lexer at construction time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position {
    /// 1-based line number.
    pub line: usize,
    /// 1-based column number (character position in the line).
    pub column: usize,
}

impl Position {
    /// Creates a new `Position`.
    #[inline]
    pub const fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }
}

/// A half-open source range: `[start, end)`.
///
/// `Span` is used to mark the region of source text that a token or AST node
/// covers, or to attach precise locations to diagnostics.
///
/// Invariants are not enforced here, but it is conventional for `start <= end`
/// in lexicographic `(line, column)` ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Starting position (inclusive).
    pub start: Position,
    /// Ending position (exclusive by convention).
    pub end: Position,
}

impl Span {
    /// Creates a new `Span`.
    #[inline]
    pub const fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }

    /// Merge two spans into one that covers both.
    ///
    /// The result’s `start` is the minimum of the two starts, and `end` is
    /// the maximum of the two ends.
    #[inline]
    pub fn merge(&self, other: &Span) -> Span {
        Span {
            start: if self.start <= other.start { self.start } else { other.start },
            end: if self.end >= other.end { self.end } else { other.end },
        }
    }

    /// Returns `true` if the span is empty (same start and end position).
    #[inline]
    pub fn is_empty(&self) -> bool {self.start == self.end}

    /// Returns the inclusive line range spanned by this `Span`.
    #[inline]
    pub fn line_range(&self) -> (usize, usize) {
        (self.start.line, self.end.line)
    }

    /// Pretty-print for diagnostics (human-readable).
    #[inline]
    pub fn display(&self) -> String {
        format!(
            "span {}:{} to {}:{}",
            self.start.line, self.start.column, self.end.line, self.end.column
        )
    }
}

/// A simple error type for parser/lexer diagnostics.
///
/// This flattened error carries only a message and an optional `Span`.
/// Use `from_err` to convert from other error types while optionally
/// attaching a span.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("{message} at {span:?}")]
pub struct ParlexError {
    /// Human-readable message.
    pub message: String,
    /// Optional source span for pinpointing the error.
    pub span: Option<Span>,
}

impl ParlexError {
    /// Convert any error into `ParlexError`, preserving an existing
    /// `ParlexError` (pass-through) and optionally attaching/overriding
    /// the span.
    ///
    /// * If `err` is already a `ParlexError`, this clones it and overwrites its
    ///   `span` when `span.is_some()`.
    /// * Otherwise, it wraps `err.to_string()` into `ParlexError` with the given `span`.
    pub fn from_err<E>(err: E, span: Option<Span>) -> Self
    where
        E: std::fmt::Display + 'static,
    {
        // `Any` is blanket-implemented for all `'static` types, so downcast is OK.
        if let Some(pe) = (&err as &dyn std::any::Any).downcast_ref::<ParlexError>() {
            let mut out = pe.clone();
            if let Some(s) = span {
                out.span = Some(s);
            }
            out
        } else {
            ParlexError { message: err.to_string(), span }
        }
    }
}

/// Build an `Option<Span>` inline from 1-based line/column coordinates.
///
/// This macro returns `Some(Span { ... })`, which is convenient for
/// populating fields like `ParlexError { span, .. }`.
///
/// # Examples
///
/// ```rust
/// # use parlex::span;
/// let s = span!(1, 1, 1, 5);
/// assert!(s.is_some());
/// ```
#[macro_export]
macro_rules! span {
    ($line_start:expr, $col_start:expr, $line_end:expr, $col_end:expr) => {
        Some($crate::Span {
            start: $crate::Position { line: $line_start, column: $col_start },
            end:   $crate::Position { line: $line_end,   column: $col_end   },
        })
    }
}
