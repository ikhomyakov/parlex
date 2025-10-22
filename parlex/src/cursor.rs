//! Span, position, and a tiny lexer cursor with line-length history.
//!
//! This module provides:
//!
//! - [`Position`] — a 0-based `(line, column)` location in source text,
//! - [`Span`] — a half-open range `[start, end)` for attaching precise locations to
//!   tokens, AST nodes, and diagnostics,
//! - [`LexerCursor`] — a minimal cursor that advances/retreats over bytes,
//!   updating a span and tracking previous line lengths,
//! - a small fixed-size ring buffer [`LineHistory<N>`] used by [`LexerCursor`] to
//!   remember line lengths at newlines,
//! - the convenience macro [`span!`] to build `Option<Span>` inline.
//!
//! ### How `LexerCursor` tracks lines
//!
//! - On `advance(b'\n')`: push the **current line length** to history,
//!   increment the line number, and reset `column` to 0.
//! - On `advance(other)`: increment `column`.
//! - On `retreat(b'\n')`: allowed only when `end.column == 0` and `end.line > 0`.
//!   Pops the previous line length from history and moves back to the end of the
//!   previous line (restoring its column).
//! - On `retreat(other)`: decrements `column` if `column > 0`, otherwise errors.
//!
//! History capacity is fixed (`LINE_HISTORY_SIZE`), which bounds how far back
//! through line breaks you can retreat.
//!
//! ### Errors
//!
//! - [`SpanError::HistoryFull`] / [`SpanError::HistoryEmpty`]: ring buffer limits,
//! - [`SpanError::UnexpectedRetreat { .. }`]: a logically invalid retreat.

use thiserror::Error;

/// A 0-based line/column position in source text.
#[derive(Debug, Clone, Default, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position {
    /// 0-based line number.
    pub line: usize,
    /// 0-based column number (character position in the line).
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
#[derive(Debug, Clone, Default, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

impl Span {
    /// Creates a new `Span`.
    #[inline]
    pub const fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }

    /// Start (or restart) this span at its current `end` position (empty span at end).
    /// Effect: span(x,y, z,w) -> span(z,w, z,w)
    pub fn collapse(&mut self) {
        self.start = self.end;
    }

    /// Merge with another span by covering both.
    pub fn merge(&self, other: &Span) -> Span {
        let start = if self.start <= other.start {
            self.start
        } else {
            other.start
        };
        let end = if self.end >= other.end {
            self.end
        } else {
            other.end
        };
        Span { start, end }
    }

    /// Is this span empty (start == end)?
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

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

/// Errors related to span tracking, line history, or cursor movement.
///
/// These errors represent exceptional conditions that may occur while
/// maintaining source positions in [`LexerCursor`] or [`LineHistory`].
///
/// # Variants
///
/// * [`HistoryEmpty`] — the line history ring buffer is empty and cannot be popped.
/// * [`UnexpectedRetreat`] — an invalid retreat operation was attempted, such as
///   moving before column 0 or before the first line.
#[derive(Debug, Clone, Error)]
pub enum SpanError {
    /// The line history buffer is empty — there is no previous line length to restore.
    #[error("span history buffer is empty")]
    HistoryEmpty,

    /// A logically invalid retreat was attempted.
    ///
    /// This may occur when:
    /// - trying to retreat on a newline when not exactly at the start of a line,
    /// - trying to retreat on a non-newline when the column is already zero.
    ///
    /// The error includes the byte that caused it and the cursor position at failure.
    #[error("unexpected span retreat in position {pos} on byte {byte}")]
    UnexpectedRetreat { byte: u8, pos: usize },
}

/// The number of previous line lengths remembered by [`LexerCursor`].
///
/// `LINE_HISTORY_SIZE` determines how many line breaks can be safely undone
/// when calling [`LexerCursor::retreat`].  
/// Once the buffer is full, pushing another newline via [`LexerCursor::advance`]
/// will return [`SpanError::HistoryFull`].
pub(crate) const LINE_HISTORY_SIZE: usize = 16;

/// A fixed-capacity history buffer that stores recent entries in a ring-like fashion.
///
/// The buffer supports `push` and `pop` operations in FIFO order and
/// automatically wraps around when reaching the end. Its capacity is fixed
/// at compile time via a const generic parameter `N`.
///
/// The buffer **never overfills**: once its configured capacity is reached,
/// pushing a new entry will overwrite the **oldest** entry in the buffer.
///
/// This design ensures constant memory usage regardless of how many entries
/// are pushed. The `capacity` therefore defines how far back you can "retreat"
/// through the history — not the maximum number of times `push` can be called.
///
/// In other words:
/// - The buffer always contains at most `N` entries.
/// - Pushing beyond capacity overwrites the oldest entries.
/// - The buffer behaves as a **ring buffer** rather than a growable list.
///
/// `LineHistory` is used internally by [`LexerCursor`] to track the length of
/// each completed line (the column count before each newline).
///
/// # Example
///
/// ```rust
/// # use parlex::{SpanError, LineHistory};
///
/// let mut h: LineHistory<2> = LineHistory::new();
/// h.push(5).unwrap();
/// h.push(7).unwrap();
/// h.push(9).unwrap();
///
/// assert_eq!(h.pop().unwrap(), 9);
/// assert_eq!(h.pop().unwrap(), 7);
/// assert!(matches!(h.pop(), Err(SpanError::HistoryEmpty)));
/// ```
#[derive(Debug, Clone)]
pub struct LineHistory<const N: usize> {
    buf: [usize; N],
    head: usize,
    len: usize,
}

impl<const N: usize> LineHistory<N> {
    /// Creates a new empty line history buffer.
    ///
    /// Initially, the buffer has zero length and all entries are set to zero.
    #[inline]
    pub fn new() -> Self {
        Self {
            buf: [0; N],
            head: 0,
            len: 0,
        }
    }

    /// Clears the buffer, discarding all stored line lengths.
    ///
    /// After calling this, both `head` and `len` are reset to zero.
    #[inline]
    pub fn clear(&mut self) {
        self.head = 0;
        self.len = 0;
    }

    /// Pushes a new line length `v` to the history.
    ///
    /// Returns an error if the buffer is already full.
    #[inline]
    pub fn push(&mut self, v: usize) -> Result<(), SpanError> {
        self.buf[self.head] = v;
        self.head = (self.head + 1) % N;
        if self.len != N {
            self.len += 1;
        }
        Ok(())
    }

    /// Pops and returns the oldest line length.
    ///
    /// Returns an error if the buffer is empty.
    #[inline]
    pub fn pop(&mut self) -> Result<usize, SpanError> {
        if self.len == 0 {
            return Err(SpanError::HistoryEmpty);
        }
        self.head = (self.head + N - 1) % N;
        self.len -= 1;
        Ok(self.buf[self.head])
    }
}

//// A simple lexical cursor tracking byte position, line, and column.
///
/// `LexerCursor` advances through input one byte at a time and updates its
/// [`Span`] accordingly. It also records line lengths to allow safe backward
/// movement across newlines.
///
/// Used primarily by lexers or parsers that need to associate spans with
/// tokens, handle backtracking, or generate diagnostics.
///
/// # Structure
///
/// * [`pos`] — absolute byte index in input (0-based)
/// * [`span`] — the current half-open region being consumed
/// * `line_history` — remembers the length of previous lines
///
/// # Example
///
/// ```rust
/// # use parlex::{LexerCursor, SpanError};
///
/// let mut cur = LexerCursor::new();
/// for &b in b"hi\n" {
///     cur.advance(b).unwrap();
/// }
/// assert_eq!(cur.span.end.line, 1);
/// assert_eq!(cur.span.end.column, 0);
///
/// // Retreat newline back to previous line
/// cur.retreat(b'\n').unwrap();
/// assert_eq!(cur.span.end.line, 0);
/// ```
#[derive(Debug, Clone)]
pub struct LexerCursor {
    /// Absolute byte position in the source (0-based).
    pub pos: usize,

    /// The current source span being updated.
    pub span: Span,

    /// Fixed-size history of previous line lengths.
    line_history: LineHistory<LINE_HISTORY_SIZE>,
}

impl LexerCursor {
    /// Creates a new cursor at position 0 with an empty span and cleared history.
    pub fn new() -> Self {
        Self {
            pos: 0,
            span: Span::default(),
            line_history: LineHistory::new(),
        }
    }

    /// Advances the cursor by one byte `b`.
    ///
    /// * If `b == '\n'`, pushes the current line length to history,
    ///   increments the line number, and resets column to 0.
    /// * Otherwise, increments the column count.
    ///
    /// Returns [`SpanError::HistoryFull`] if the history buffer is full.
    pub fn advance(&mut self, b: u8) -> Result<(), SpanError> {
        if b == b'\n' {
            self.line_history.push(self.span.end.column)?;
            self.span.end.line += 1;
            self.span.end.column = 0;
        } else {
            self.span.end.column += 1;
        }
        self.pos += 1;
        Ok(())
    }

    /// Retreats the cursor by undoing one previously consumed byte `b`.
    ///
    /// * If `b == '\n'` and currently at the start of a line (`column == 0`),
    ///   pops the previous line length and moves back to that line.
    /// * If `b != '\n'`, decrements the column if possible.
    ///
    /// Returns [`SpanError::UnexpectedRetreat`] if moving before column 0 or
    /// before the first line, or [`SpanError::HistoryEmpty`] if no prior line
    /// data is available to restore.
    pub fn retreat(&mut self, b: u8) -> Result<(), SpanError> {
        if b == b'\n' {
            if self.span.end.line != 0 && self.span.end.column == 0 {
                self.span.end.line -= 1;
                self.span.end.column = self.line_history.pop()?;
            } else {
                return Err(SpanError::UnexpectedRetreat {
                    byte: b,
                    pos: self.pos,
                });
            }
        } else {
            if self.span.end.column != 0 {
                self.span.end.column -= 1;
            } else {
                return Err(SpanError::UnexpectedRetreat {
                    byte: b,
                    pos: self.pos,
                });
            }
        }

        if self.pos != 0 {
            self.pos -= 1;
        } else {
            return Err(SpanError::UnexpectedRetreat {
                byte: b,
                pos: self.pos,
            });
        }

        if self.span.start > self.span.end {
            self.span.start = self.span.end;
        }

        Ok(())
    }
}

/// Build an `Span` inline from 0-based line/column coordinates.
///
/// This macro returns `Span { ... }`, which is convenient for
/// populating fields like `ParlexError { span, .. }`.
///
/// # Examples
///
/// ```rust
/// # use parlex::span;
/// let s = span!(0, 0, 1, 4);
/// assert_eq!(s.unwrap().end.column, 4);
/// ```
#[macro_export]
macro_rules! span {
    ($line_start:expr, $col_start:expr, $line_end:expr, $col_end:expr) => {
        Some($crate::Span {
            start: $crate::Position {
                line: $line_start,
                column: $col_start,
            },
            end: $crate::Position {
                line: $line_end,
                column: $col_end,
            },
        })
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_history_push_pop_fifo_behavior() {
        let mut h: super::LineHistory<3> = super::LineHistory::new();
        assert!(matches!(h.pop(), Err(SpanError::HistoryEmpty)));

        h.push(1).unwrap();
        dbg!(&h);
        h.push(2).unwrap();
        dbg!(&h);
        h.push(3).unwrap();
        dbg!(&h);
        h.push(4).unwrap();
        dbg!(&h);

        assert_eq!(h.pop().unwrap(), 4);
        dbg!(&h);
        assert_eq!(h.pop().unwrap(), 3);
        dbg!(&h);
        assert_eq!(h.pop().unwrap(), 2);
        assert!(matches!(h.pop(), Err(SpanError::HistoryEmpty)));
    }

    #[test]
    fn line_history_wraparound_indexing() {
        let mut h: super::LineHistory<2> = super::LineHistory::new();

        h.push(10).unwrap();
        assert_eq!(h.pop().unwrap(), 10);

        h.push(20).unwrap();
        h.push(30).unwrap();
        h.push(40).unwrap();

        assert_eq!(h.pop().unwrap(), 40);
        assert_eq!(h.pop().unwrap(), 30);
        assert!(matches!(h.pop(), Err(SpanError::HistoryEmpty)));
    }

    #[test]
    fn line_history_clear_resets_to_empty() {
        let mut h: super::LineHistory<2> = super::LineHistory::new();
        h.push(7).unwrap();
        h.push(8).unwrap();
        h.clear();
        assert!(matches!(h.pop(), Err(SpanError::HistoryEmpty)));
        h.push(9).unwrap();
        assert_eq!(h.pop().unwrap(), 9);
    }

    #[test]
    fn cursor_advance_simple_bytes_increments_column_and_pos() {
        let mut cur = LexerCursor::new();
        for (i, &b) in b"xyz".iter().enumerate() {
            cur.advance(b).unwrap();
            assert_eq!(cur.span.end.line, 0);
            assert_eq!(cur.span.end.column, i + 1);
            assert_eq!(cur.pos, i + 1);
        }
    }

    #[test]
    fn cursor_advance_newline_records_line_length_and_moves_to_next_line() {
        let mut cur = LexerCursor::new();
        for &b in b"ab".iter() {
            cur.advance(b).unwrap();
        }
        assert_eq!(cur.span.end, Position::new(0, 2));
        cur.advance(b'\n').unwrap();
        assert_eq!(cur.span.end, Position::new(1, 0));
        // next bytes now advance column on line 1
        cur.advance(b'c').unwrap();
        cur.advance(b'd').unwrap();
        assert_eq!(cur.span.end, Position::new(1, 2));
        assert_eq!(cur.pos, 5);
    }

    #[test]
    fn cursor_retreat_non_newline_decrements_column_or_errors_at_zero() {
        let mut cur = LexerCursor::new();
        cur.advance(b'a').unwrap();
        cur.advance(b'b').unwrap();
        assert_eq!(cur.span.end, Position::new(0, 2));

        cur.retreat(b'b').unwrap();
        assert_eq!(cur.span.end, Position::new(0, 1));

        cur.retreat(b'a').unwrap();
        assert_eq!(cur.span.end, Position::new(0, 0));

        // At col 0; retreating non-newline must error.
        let err = cur.retreat(b'x').unwrap_err();
        assert!(
            matches!(err, SpanError::UnexpectedRetreat { byte, pos } if byte == b'x' && pos == 0)
        );
    }

    #[test]
    fn cursor_retreat_newline_requires_start_of_line() {
        let mut cur = LexerCursor::new();
        // Go to line 1, col 1: "a\nb"
        cur.advance(b'a').unwrap();
        cur.advance(b'\n').unwrap(); // line 1, col 0
        cur.advance(b'b').unwrap(); // line 1, col 1

        // Trying to retreat a newline while not at col 0 is illegal.
        let err = cur.retreat(b'\n').unwrap_err();
        assert!(matches!(err, SpanError::UnexpectedRetreat { .. }));

        // Retreat the 'b', then newline is allowed.
        cur.retreat(b'b').unwrap();
        assert_eq!(cur.span.end, Position::new(1, 0));
        cur.retreat(b'\n').unwrap();
        assert_eq!(cur.span.end, Position::new(0, 1)); // restored previous line length
    }

    #[test]
    fn cursor_multiple_lines_and_full_history_error() {
        let mut cur = LexerCursor::new();

        for &c in &[b'a'; LINE_HISTORY_SIZE] {
            cur.advance(c).unwrap();
            cur.advance(b'\n').unwrap(); // pushes line length
        }

        cur.advance(b'b').unwrap();
        cur.advance(b'\n').unwrap();
    }

    #[test]
    fn cursor_retreat_across_many_newlines_restores_columns_fifo() {
        let mut cur = LexerCursor::new();

        // Lines with varying lengths
        for &b in b"ab\nx\nwxyz\n" {
            cur.advance(b).unwrap();
        }
        assert_eq!(cur.span.end, Position::new(3, 0));

        // Retreat newline -> back to line 2, restore col 4
        cur.retreat(b'\n').unwrap();
        assert_eq!(cur.span.end, Position::new(2, 4));

        // Retreat 4 chars -> col 0
        for &b in b"zyxw" {
            cur.retreat(b).unwrap();
        }
        assert_eq!(cur.span.end, Position::new(2, 0));

        // Retreat newline -> back to line 1, restore its length (1)
        cur.retreat(b'\n').unwrap();
        assert_eq!(cur.span.end, Position::new(1, 1));

        // Retreat 'x'
        cur.retreat(b'x').unwrap();
        assert_eq!(cur.span.end, Position::new(1, 0));

        // Retreat newline -> back to line 0, restore length 2
        cur.retreat(b'\n').unwrap();
        assert_eq!(cur.span.end, Position::new(0, 2));
    }

    #[test]
    fn cursor_start_never_exceeds_end_after_retreat() {
        let mut cur = LexerCursor::new();
        for &b in b"foo" {
            cur.advance(b).unwrap();
        }
        // Force start beyond end, then ensure retreat fixes it.
        cur.span.start = Position::new(0, 10);
        cur.retreat(b'o').unwrap();
        assert!(cur.span.start <= cur.span.end);
        assert_eq!(cur.span.start, cur.span.end);
    }

    #[test]
    fn cursor_pos_tracks_total_bytes_advanced_minus_retreats() {
        let mut cur = LexerCursor::new();
        for &b in b"abc\ndef" {
            // allow potential HistoryFull if LINE_HISTORY_SIZE shrinks
            let _ = cur.advance(b);
        }
        let pos_after = cur.pos;

        // Retreat three bytes
        cur.retreat(b'f').unwrap();
        cur.retreat(b'e').unwrap();
        cur.retreat(b'd').unwrap();

        assert_eq!(cur.pos, pos_after - 3);
    }

    #[test]
    fn cursor_illegal_newline_retreat_on_first_line_errors() {
        let mut cur = LexerCursor::new();
        // at (0,0), trying to retreat newline must fail
        let err = cur.retreat(b'\n').unwrap_err();
        assert!(matches!(err, SpanError::UnexpectedRetreat { .. }));
    }

    #[test]
    fn span_macro_can_be_unwrapped_and_displayed() {
        let s = span!(10, 20, 11, 0).unwrap();
        assert_eq!(s.display(), "span 10:20 to 11:0");
    }

    #[test]
    fn span_macro_values_are_ordered_lexicographically_by_type_impl() {
        // Ordering is derived on Span/Position; the macro just constructs values.
        let a = span!(0, 0, 0, 1).unwrap();
        let b = span!(0, 0, 0, 2).unwrap();
        assert!(a < b);
        assert!(b > a);
    }

    #[test]
    fn span_macro_works_with_large_indices() {
        let big = usize::MAX / 2;
        let s = span!(big, big - 1, big, big).unwrap();
        assert_eq!(s.start, Position::new(big, big - 1));
        assert_eq!(s.end, Position::new(big, big));
    }

    #[test]
    fn span_macro_is_compatible_with_merge_logic() {
        let a = span!(0, 2, 1, 3).unwrap();
        let b = span!(0, 1, 2, 0).unwrap();
        let m = a.merge(&b);
        assert_eq!(m.start, Position::new(0, 1));
        assert_eq!(m.end, Position::new(2, 0));
    }

    #[test]
    fn span_macro_collapsing_behavior_after_construction() {
        let mut s = span!(4, 0, 4, 5).unwrap();
        assert!(!s.is_empty());
        s.collapse();
        assert!(s.is_empty());
        assert_eq!(s.start, Position::new(4, 5));
        assert_eq!(s.end, Position::new(4, 5));
    }

    #[test]
    fn span_macro_compares_equal_for_identical_inputs() {
        let a = span!(3, 3, 5, 8).unwrap();
        let b = span!(3, 3, 5, 8).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn span_macro_option_chaining_example() {
        // Demonstrates ergonomic use when a function returns Option<Span>
        fn maybe_span(flag: bool) -> Option<Span> {
            if flag { span!(0, 0, 0, 1) } else { None }
        }
        assert!(maybe_span(true).is_some());
        assert!(maybe_span(false).is_none());
    }
}
