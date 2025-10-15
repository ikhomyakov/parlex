//! # symtab
//!
//! A minimal, flat symbol table built on [`indexmap::IndexMap`].
//!
//! This table assigns each unique string name a stable integer index.
//! You can use it to *intern* symbols (insert if missing and get index)
//! and later access their values by index.
//!
//! ## Example
//! ```rust
//! # use parlex_calc::SymTab;
//! let mut st = SymTab::new();
//! let i = st.intern("foo"); // inserts "foo" at index 0
//! assert_eq!(st.get(i).unwrap(), 0);
//! st.set(i, 42).unwrap();
//! assert_eq!(st.get(i).unwrap(), 42);
//! assert_eq!(st.intern("foo"), i); // same index, not reinserted
//! ```

use indexmap::{IndexMap, map::Entry};
use smartstring::alias::String;
use thiserror::Error;

/// Errors that can occur when operating on a [`SymTab`].
#[derive(Debug, Error)]
pub enum SymTabError {
    /// Attempted to access an invalid index (out of bounds).
    #[error("invalid symbol index {index} (table length {len})")]
    InvalidIndex {
        /// The index that was requested.
        index: usize,
        /// The number of entries currently in the table.
        len: usize,
    },
}

/// A simple symbol table that maps string names to integer values.
///
/// Each inserted name receives a stable index corresponding to its insertion order.
/// Re-inserting the same name returns the existing index.
#[derive(Debug)]
pub struct SymTab {
    tab: IndexMap<String, i64>,
}

impl SymTab {
    /// Creates a new, empty symbol table.
    pub fn new() -> Self {
        Self {
            tab: IndexMap::new(),
        }
    }

    /// Returns the number of entries currently stored in the symbol table.
    ///
    /// Each entry corresponds to a unique symbol (e.g., variable or identifier)
    /// that has been interned.
    ///
    /// # Example
    /// ```rust
    /// # use parlex_calc::SymTab;
    /// let mut symtab = SymTab::new();
    /// assert_eq!(symtab.len(), 0);
    /// symtab.intern("foo");
    /// assert_eq!(symtab.len(), 1);
    /// symtab.intern("baz");
    /// assert_eq!(symtab.len(), 2);
    /// symtab.intern("foo");
    /// assert_eq!(symtab.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.tab.len()
    }

    /// Inserts the given name if it doesn't exist and returns its index.
    ///
    /// If the name already exists, this returns the existing index
    /// without modifying the stored value.
    ///
    /// # Examples
    /// ```
    /// # use parlex_calc::SymTab;
    /// let mut st = SymTab::new();
    /// let i = st.intern("a");
    /// assert_eq!(i, 0);
    /// assert_eq!(st.intern("a"), 0); // existing index
    /// ```
    pub fn intern(&mut self, name: impl AsRef<str>) -> usize {
        match self.tab.entry(String::from(name.as_ref())) {
            Entry::Occupied(o) => o.index(),
            Entry::Vacant(v) => {
                let o = v.insert_entry(0);
                o.index()
            }
        }
    }

    /// Updates the value at the given index.
    ///
    /// Returns [`Err`] if the index is out of bounds.
    ///
    /// # Examples
    /// ```
    /// # use parlex_calc::SymTab;
    /// let mut st = SymTab::new();
    /// let i = st.intern("x");
    /// st.set(i, 123).unwrap();
    /// assert_eq!(st.get(i).unwrap(), 123);
    /// ```
    pub fn set(&mut self, index: usize, new_value: i64) -> Result<(), SymTabError> {
        let n = self.tab.len();
        let (_, value) = self
            .tab
            .get_index_mut(index)
            .ok_or(SymTabError::InvalidIndex { index, len: n })?;
        *value = new_value;
        Ok(())
    }

    /// Returns the value stored at the given index.
    ///
    /// Returns [`Err`] if the index is out of bounds.
    pub fn get(&self, index: usize) -> Result<i64, SymTabError> {
        let (_, value) = self.tab.get_index(index).ok_or(SymTabError::InvalidIndex {
            index,
            len: self.tab.len(),
        })?;
        Ok(*value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_table_is_empty() {
        let st = SymTab::new();
        assert_eq!(st.len(), 0);
    }

    #[test]
    fn intern_assigns_sequential_indices() {
        let mut st = SymTab::new();
        let a = st.intern("a");
        let b = st.intern("b");
        let c = st.intern("c");
        assert_eq!((a, b, c), (0, 1, 2));
        assert_eq!(st.len(), 3);
    }

    #[test]
    fn re_intern_returns_same_index_and_preserves_value() {
        let mut st = SymTab::new();
        let i = st.intern("x");
        st.set(i, 42).unwrap();

        let j = st.intern("x"); // should NOT overwrite the stored value
        assert_eq!(i, j);
        assert_eq!(st.get(i).unwrap(), 42);
    }

    #[test]
    fn set_and_get_roundtrip() {
        let mut st = SymTab::new();
        let i = st.intern("n");
        st.set(i, -7).unwrap();
        assert_eq!(st.get(i).unwrap(), -7);

        st.set(i, 123).unwrap();
        assert_eq!(st.get(i).unwrap(), 123);
    }

    #[test]
    fn get_invalid_index_errors() {
        let mut st = SymTab::new();
        let _ = st.intern("only_one");
        match st.get(5) {
            Err(SymTabError::InvalidIndex { index, len }) => {
                assert_eq!(index, 5);
                assert_eq!(len, 1);
            }
            other => panic!("expected InvalidIndex, got {:?}", other),
        }
    }

    #[test]
    fn set_invalid_index_errors() {
        let st_len;
        let mut st = SymTab::new();
        let _ = st.intern("z");
        st_len = st.len();
        let err = st.set(999, 1).unwrap_err();
        match err {
            SymTabError::InvalidIndex { index, len } => {
                assert_eq!(index, 999);
                assert_eq!(len, st_len);
            }
        }
    }

    #[test]
    fn intern_same_name_multiple_times_does_not_change_len() {
        let mut st = SymTab::new();
        let first = st.intern("dup");
        let second = st.intern("dup");
        let third = st.intern("dup");
        assert_eq!(first, second);
        assert_eq!(second, third);
        assert_eq!(st.len(), 1);
    }

    #[test]
    fn many_symbols_have_distinct_indices() {
        let mut st = SymTab::new();
        let mut seen = std::collections::BTreeSet::new();
        for n in 0..100 {
            let name = format!("v{n}");
            let idx = st.intern(name);
            assert!(seen.insert(idx), "duplicate index {}", idx);
        }
        assert_eq!(st.len(), 100);
        assert_eq!(seen.len(), 100);
    }
}
