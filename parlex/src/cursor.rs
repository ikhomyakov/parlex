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

#[derive(Debug, Clone, Error)]
pub enum SpanError {
    #[error("span history buffer is full")]
    HistoryFull,
    #[error("span history buffer is empty")]
    HistoryEmpty,
    #[error("unexpected span retreat")]
    UnexpectedRetreat,
}

const LINE_HISTORY_SIZE: usize = 10;

#[derive(Debug, Clone)]
struct LineHistory<const N: usize> {
    buf: [usize; N],
    head: usize,
    len: usize,
}

impl<const N: usize> LineHistory<N> {
    #[inline]
    fn new() -> Self {
        Self {
            buf: [0; N],
            head: 0,
            len: 0,
        }
    }

    #[inline]
    fn clear(&mut self) {
        self.head = 0;
        self.len = 0;
    }

    #[inline]
    fn push(&mut self, v: usize) -> Result<(), SpanError> {
        if self.len == N {
            return Err(SpanError::HistoryFull);
        }
        self.buf[self.head] = v;
        self.head = (self.head + 1) % N;
        self.len += 1;
        Ok(())
    }

    #[inline]
    fn pop(&mut self) -> Result<usize, SpanError> {
        if self.len == 0 {
            return Err(SpanError::HistoryEmpty);
        }
        self.head = (self.head + N - 1) % N;
        self.len -= 1;
        Ok(self.buf[self.head])
    }
}

/// Tracks current lexical position and maintains line history.
///
/// `LexerCursor` advances and retreats over input, updating a `Span` and
/// tracking line lengths across newlines.
#[derive(Debug, Clone)]
pub struct LexerCursor {
    pub pos: usize,
    pub span: Span,
    line_history: LineHistory<LINE_HISTORY_SIZE>,
}

impl LexerCursor {
    pub fn new() -> Self {
        Self {
            pos: 0,
            span: Span::default(),
            line_history: LineHistory::new(),
        }
    }

    /// Advance by consuming a byte `b`, updating span and line history.
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

    /// Retreat by undoing one byte `b`, updating span and line history.
    pub fn retreat(&mut self, b: u8) -> Result<(), SpanError> {
        if b == b'\n' {
            if self.span.end.line != 1 && self.span.end.column == 0 {
                self.span.end.line -= 1;
                self.span.end.column = self.line_history.pop()?;
            } else {
                return Err(SpanError::UnexpectedRetreat);
            }
        } else {
            if self.span.end.column != 0 {
                self.span.end.column -= 1;
            } else {
                return Err(SpanError::UnexpectedRetreat);
            }
        }
        self.pos -= 1;
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
