use crate::Span;
use thiserror::Error;
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
            ParlexError {
                message: err.to_string(),
                span,
            }
        }
    }
}
