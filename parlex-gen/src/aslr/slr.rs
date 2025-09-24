// This module defines LR(0) item machinery, FIRST/FOLLOW computations,
// and SLR(1) parse table construction.

use std::collections::BTreeSet;
use std::io::{self, Write};

/// An LR(0) item: production index + dot position
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Item {
    pub prod: usize,
    pub dot: usize,
}

/// A set of LR(0) items
pub type ItemSet = BTreeSet<Item>;
/// The canonical collection of item-sets
pub type ItemSetSet = BTreeSet<ItemSet>;

pub fn closure(items: &ItemSet, prods: &[Vec<usize>], n_nonterm: usize) -> ItemSet {
    let mut c = items.clone();
    let mut inserted = true;
    while inserted {
        inserted = false;
        // Iterate over a snapshot to avoid borrowing issues
        for item in c.clone().into_iter() {
            // If dot position points to a symbol
            if item.dot < prods[item.prod].len() {
                let t = prods[item.prod][item.dot];
                // If it's a non-terminal, add its productions
                if t < n_nonterm {
                    for (j, p) in prods.iter().enumerate() {
                        if p[0] == t {
                            let new_item = Item { prod: j, dot: 1 };
                            if c.insert(new_item.clone()) {
                                inserted = true;
                            }
                        }
                    }
                }
            }
        }
    }
    c
}

pub fn goto(items: &ItemSet, sym: usize, prods: &[Vec<usize>], n_nonterm: usize) -> ItemSet {
    let mut moved = ItemSet::new();
    for item in items {
        let p = &prods[item.prod];
        if item.dot < p.len() && p[item.dot] == sym {
            moved.insert(Item {
                prod: item.prod,
                dot: item.dot + 1,
            });
        }
    }
    closure(&moved, prods, n_nonterm)
}

pub fn construct_set(prods: &[Vec<usize>], n_nonterm: usize, n_term: usize) -> ItemSetSet {
    let mut c = ItemSetSet::new();
    // Start closure on initial item (prod 0, dot at 1)
    let start0 = ItemSet::from([Item { prod: 0, dot: 1 }]);
    c.insert(closure(&start0, prods, n_nonterm));
    let mut changed = true;
    while changed {
        changed = false;
        for state in c.clone().into_iter() {
            for sym in 0..(n_nonterm + n_term) {
                let nxt = goto(&state, sym, prods, n_nonterm);
                if !nxt.is_empty() && c.insert(nxt) {
                    changed = true;
                }
            }
        }
    }
    c
}

pub fn write_set<W: Write>(
    out: &mut W,
    c: &ItemSetSet,
    prods: &[Vec<usize>],
    tokens: &[String],
) -> io::Result<()> {
    writeln!(out, "CS,{}\n", c.len())?;
    for (i, state) in c.iter().enumerate() {
        for item in state {
            write!(out, "C,{},", i)?;
            let p = &prods[item.prod];
            for (j, t) in p.iter().enumerate() {
                if j == item.dot {
                    write!(out, ". ")?;
                }
                write!(out, "{} ", tokens[*t])?;
                if j == 0 {
                    write!(out, "-> ")?;
                }
            }
            if p.len() == item.dot {
                write!(out, ". ")?;
            }
            writeln!(out, "")?;
        }
        writeln!(out, "")?;
    }
    Ok(())
}

pub fn write_prods<W: Write>(
    out: &mut W,
    prods: &[Vec<usize>],
    tokens: &[String],
) -> io::Result<()> {
    writeln!(out, "PS,{}\n", prods.len())?;
    for (i, prod) in prods.iter().enumerate() {
        write!(out, "P,{},", i)?;
        for (j, t) in prod.iter().enumerate() {
            write!(out, "{} ", tokens[*t])?;
            if j == 0 {
                write!(out, "-> ")?;
            }
        }
        writeln!(out)?;
    }
    Ok(())
}

pub fn write_fstflw<W: Write>(
    out: &mut W,
    vs: &[BTreeSet<usize>],
    nullable: Option<&[bool]>,
    tokens: &[String],
) -> io::Result<()> {
    let (label, nullable) = match nullable {
        Some(nullable) => ("FIRST", nullable.to_vec()),
        None => ("FOLLOW", vec![false; vs.len()]),
    };

    for (sym, set) in vs.iter().enumerate() {
        let dname = format!("${}", sym);
        let name = tokens.get(sym).unwrap_or(&dname);

        write!(out, "{},{},{{", label, name)?;

        if nullable[sym] {
            write!(out, "`empty', ")?;
        }

        for &t in set {
            let dname = format!("${}", t);
            let tname = tokens.get(t).unwrap_or(&dname);
            write!(out, "{}, ", tname)?;
        }

        writeln!(out, "}}")?;
    }

    Ok(())
}

/// Compute FIRST sets and nullability for all symbols
pub fn first_sets(
    prods: &[Vec<usize>],
    n_nonterm: usize,
    n_term: usize,
) -> (Vec<BTreeSet<usize>>, Vec<bool>) {
    let n_sym = n_nonterm + n_term;
    let mut first: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n_sym];
    let mut nullable = vec![false; n_sym];
    // Terminals: FIRST(t) = {t}
    for t in n_nonterm..n_sym {
        first[t].insert(t);
    }
    let mut changed = true;
    while changed {
        changed = false;
        for prod in prods {
            let lhs = prod[0];
            if prod.len() == 1 {
                // ε-production
                if !nullable[lhs] {
                    nullable[lhs] = true;
                    changed = true;
                }
            } else {
                let mut all_nullable = true;
                for &sym in &prod[1..] {
                    // Clone FIRST(sym) to avoid simultaneous borrow
                    let first_sym = first[sym].clone();
                    for f in first_sym {
                        if first[lhs].insert(f) {
                            changed = true;
                        }
                    }
                    if !nullable[sym] {
                        all_nullable = false;
                        break;
                    }
                }
                if all_nullable && !nullable[lhs] {
                    nullable[lhs] = true;
                    changed = true;
                }
            }
        }
    }
    (first, nullable)
}

/// Compute FOLLOW sets for non-terminals
pub fn follow_sets(
    prods: &[Vec<usize>],
    n_nonterm: usize,
    n_term: usize,
    start_sym: usize,
    first: &Vec<BTreeSet<usize>>,
    nullable: &Vec<bool>,
) -> Vec<BTreeSet<usize>> {
    let eos = n_nonterm + n_term - 1;
    let mut follow: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n_nonterm];
    // EOF marker at start symbol
    follow[start_sym].insert(eos);
    let mut changed = true;
    while changed {
        changed = false;
        for prod in prods {
            let lhs = prod[0];
            let rhs = &prod[1..];
            for i in 0..rhs.len() {
                let b = rhs[i];
                if b < n_nonterm {
                    // Compute FIRST of beta
                    let mut beta_nullable = true;
                    let mut first_beta = BTreeSet::new();
                    for &sym in &rhs[i + 1..] {
                        let first_sym = first[sym].clone();
                        for f in first_sym {
                            first_beta.insert(f);
                        }
                        if !nullable[sym] {
                            beta_nullable = false;
                            break;
                        }
                    }
                    // Add FIRST(beta) to FOLLOW(b)
                    for &f in &first_beta {
                        if follow[b].insert(f) {
                            changed = true;
                        }
                    }
                    // If beta nullable, add FOLLOW(lhs) to FOLLOW(b)
                    if beta_nullable {
                        let follow_lhs = follow[lhs].clone();
                        for f in follow_lhs {
                            if follow[b].insert(f) {
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }
    follow
}

/// Find the index of a state in the collection (or -1)
fn find_state(c: &ItemSetSet, target: &ItemSet) -> Option<usize> {
    for (i, st) in c.iter().enumerate() {
        if st == target {
            return Some(i);
        }
    }
    None
}

/// Token action types
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ActTyp {
    _Error = 0,
    Accept = 1,
    Shift = 2,
    Reduce = 3,
    _Ambig = 4,
    Goto = 5,
}

impl ActTyp {
    pub fn to_str(self) -> &'static str {
        match self {
            ActTyp::_Error => "Error",
            ActTyp::Accept => "Accept",
            ActTyp::Shift => "Shift",
            ActTyp::Reduce => "Reduce",
            ActTyp::_Ambig => "Ambig",
            ActTyp::Goto => "Goto",
        }
    }
}

/// A parse action
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Act {
    pub typ: ActTyp,
    pub val: usize,
}

impl Act {
    pub fn new(typ: ActTyp, val: usize) -> Self {
        Act { typ, val }
    }
    pub fn val_to_string(&self, prod_enums: &[String]) -> Option<String> {
        match self.typ {
            ActTyp::_Error => None,
            ActTyp::Accept => None,
            ActTyp::Shift => Some(format!("StateID({})", self.val)),
            ActTyp::Reduce => Some(format!("ProdID::{}", prod_enums[self.val])),
            ActTyp::_Ambig => Some(format!("AmbigID({})", self.val)),
            ActTyp::Goto => Some(format!("StateID({})", self.val)),
        }
    }
}

/// SLR(1) parse table: rows states, cols tokens
pub type Tab = Vec<Vec<BTreeSet<Act>>>;

/// Construct SLR(1) parse table following the reference C++ API
pub fn construct_slr(
    c: &ItemSetSet,
    flw: &[BTreeSet<usize>],
    prods: &[Vec<usize>],
    n_nonterm: usize,
    n_term: usize,
) -> Tab {
    let size = c.len();
    let mut tab: Tab = Vec::with_capacity(size);
    tab.resize(size, Vec::new());
    for row in tab.iter_mut() {
        row.resize(n_nonterm + n_term, BTreeSet::new());
    }

    // Fill GOTO for non-terminals
    for sym in 1..(n_nonterm) {
        for (state, ssi) in c.iter().enumerate() {
            let nxt = goto(ssi, sym, prods, n_nonterm);
            if let Some(ns) = find_state(c, &nxt) {
                tab[state][sym].insert(Act::new(ActTyp::Goto, ns));
            }
        }
    }

    // Fill SHIFT and REDUCE and ACCEPT for terminals
    for sym in n_nonterm..(n_nonterm + n_term) {
        for (state, ssi) in c.iter().enumerate() {
            for item in ssi {
                let p = &prods[item.prod];
                if item.dot < p.len() && p[item.dot] == sym {
                    let nxt = goto(ssi, sym, prods, n_nonterm);
                    if let Some(ns) = find_state(c, &nxt) {
                        tab[state][sym].insert(Act::new(ActTyp::Shift, ns));
                    }
                } else if item.dot == p.len() {
                    let ltok = p[0];
                    if ltok == 0 && p.len() == 2 && p[1] == 1 {
                        // Accept on EOF token (last column)
                        tab[state][n_nonterm + n_term - 1].insert(Act::new(ActTyp::Accept, 0));
                    } else if ltok < flw.len() {
                        for &t in &flw[ltok] {
                            tab[state][t].insert(Act::new(ActTyp::Reduce, item.prod));
                        }
                    }
                }
            }
        }
    }
    tab
}
