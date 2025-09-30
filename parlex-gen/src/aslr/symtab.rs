use std::collections::HashMap;
use std::slice::Iter;

#[derive(Default, Debug)]
pub struct Symtab {
    map: HashMap<String, usize>,
    vec: Vec<String>,
}

impl Symtab {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            vec: Vec::new(),
        }
    }

    pub fn add(&mut self, sym: &str) -> usize {
        if let Some(&idx) = self.map.get(sym) {
            return idx;
        }
        let idx = self.vec.len();
        let owned = sym.to_owned();
        self.vec.push(owned.clone());
        self.map.insert(owned, idx);
        idx
    }

    pub fn iter(&self) -> Iter<'_, String> {
        self.vec.iter()
    }

    pub fn vec(&self) -> Vec<String> {
        self.vec.clone()
    }

    pub fn extend(&mut self, tab: &Symtab) {
        self.vec.extend_from_slice(&tab.vec);
    }

    pub fn _idx(&self, sym: &str) -> Option<usize> {
        self.map.get(sym).copied()
    }

    pub fn sym(&self, idx: usize) -> Option<&str> {
        self.vec.get(idx).map(|x| x.as_str())
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn _print(&self) {
        for (i, s) in self.vec.iter().enumerate() {
            println!("{}: {}", i, s);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Symtab;

    #[test]
    fn test_new_is_empty() {
        let st = Symtab::new();
        assert_eq!(st._idx("anything"), None);
        assert_eq!(st.sym(0), None);
    }

    #[test]
    fn test_add_and_retrieve() {
        let mut st = Symtab::new();
        let i_foo = st.add("foo");
        assert_eq!(i_foo, 0);
        assert_eq!(st._idx("foo"), Some(0));
        assert_eq!(st.sym(0), Some("foo"));

        let i_bar = st.add("bar");
        assert_eq!(i_bar, 1);
        assert_eq!(st._idx("bar"), Some(1));
        assert_eq!(st.sym(1), Some("bar"));
    }

    #[test]
    fn test_duplicate_add_returns_same_index() {
        let mut st = Symtab::new();
        let first = st.add("dup");
        let second = st.add("dup");
        assert_eq!(first, second);
        assert_eq!(st._idx("dup"), Some(first));
        assert_eq!(st.sym(first), Some("dup"));
        // only one unique entry
        assert_eq!(st.sym(1), None); // nothing else was inserted
    }

    #[test]
    fn test_nonexistent_lookup() {
        let mut st = Symtab::new();
        st.add("existing");
        assert_eq!(st._idx("missing"), None);
        assert_eq!(st.sym(42), None);
    }

    #[test]
    fn test_many_symbols_and_consistency() {
        let mut st = Symtab::new();
        let names = ["a", "b", "c", "a", "d", "b"];
        let mut seen = std::collections::HashSet::new();
        for &name in &names {
            let idx = st.add(name);
            assert_eq!(st.sym(idx), Some(name));
            seen.insert(name);
        }
        // number of unique symbols should equal size of seen
        assert_eq!(st.vec.len(), seen.len());
        // all stored symbols are retrievable via idx
        for name in seen {
            let idx = st._idx(name).expect("should have index");
            assert_eq!(st.sym(idx), Some(name));
        }
    }
}
