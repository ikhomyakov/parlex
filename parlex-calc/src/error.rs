//! # Calculator Error Type
//!
//! This module defines [`CalcError`], a unified error enum for the calculator
//! pipeline. It aggregates failures from:
//!
//! - **Numeric parsing** (string → integer),
//! - **UTF-8 decoding** (bytes → `String`),
//! - **Symbol-table operations** (lookups/updates).
//!
//! Conversions from underlying error types are derived with `#[from]`, enabling
//! ergonomic propagation via the `?` operator in functions that return
//! `Result<T, CalcError>`.
use crate::SymTabError;
use thiserror::Error;

/// Represents all possible errors that can occur within the calculator.
///
/// [`CalcError`] provides a single error surface for higher-level functions.
/// Each variant wraps a more specific underlying error, and thanks to `#[from]`
/// you can write `?` at call sites without explicit mapping.
///
/// # Typical sources
///
/// - [`CalcError::ParseInt`]: converting a numeric token’s text to an integer.
/// - [`CalcError::FromUtf8`]: decoding raw input bytes as UTF-8 text.
/// - [`CalcError::SymTab`]: interacting with the symbol table.
///
/// # Examples
/// Propagating a parse failure:
/// ```rust
/// # use parlex_calc::CalcError;
/// # fn demo(s: &str) -> Result<i64, CalcError> {
/// let n: i64 = s.parse()?; // ParseIntError -> CalcError via #[from]
/// # Ok(n) }
/// ```
///
/// Wrapping a symbol-table error:
/// ```rust
/// # use parlex_calc::{CalcError, SymTabError};
/// let underlying = SymTabError::InvalidIndex { index: 10, len: 3 };
/// let err: CalcError = underlying.into();
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

#[cfg(test)]
mod tests {
    use super::*;

    fn _assert_error_trait_obj(e: &dyn std::error::Error) -> &dyn std::error::Error {
        e
    }

    #[test]
    fn parse_int_maps_to_calc_error() {
        let res: Result<i64, CalcError> = "notanumber".parse::<i64>().map_err(CalcError::from);
        let err = res.unwrap_err();
        assert!(matches!(err, CalcError::ParseInt(_)));

        // Also confirm it’s a std::error::Error
        let _ = _assert_error_trait_obj(&err);
        // Display should contain our prefix
        let msg = err.to_string();
        assert!(msg.contains("unable to parse"));
    }

    #[test]
    fn from_utf8_maps_to_calc_error() {
        let bytes = vec![0xf0, 0x28, 0x8c, 0x28]; // invalid UTF-8
        let res: Result<String, CalcError> = String::from_utf8(bytes).map_err(CalcError::from);
        let err = res.unwrap_err();
        assert!(matches!(err, CalcError::FromUtf8(_)));
        assert!(err.to_string().contains("utf8 error"));
    }

    #[test]
    fn symtab_error_maps_to_calc_error() {
        let underlying = SymTabError::InvalidIndex { index: 10, len: 3 };
        let err: CalcError = underlying.into();
        assert!(matches!(err, CalcError::SymTab(_)));
        assert!(err.to_string().contains("symtab error"));
    }

    // Compile-time trait bounds sanity check.
    // If CalcError ever stops being Send + Sync + 'static these will fail to compile.
    fn _assert_send_sync_static<T: Send + Sync + 'static>() {}
    #[test]
    fn calc_error_is_send_sync_static() {
        _assert_send_sync_static::<CalcError>();
    }
}
