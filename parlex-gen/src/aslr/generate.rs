use super::lexer::{LexContext, Lexer};
use super::parser::{Production, Symbol};
use super::symtab::Symtab;
use super::{parser, slr};
use anyhow::Result;
use chumsky::Parser;
use std::io::Write;
use std::path::Path;

fn capitalize_first(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
    }
}

fn calculate_minimum_unsigned_type(n: usize) -> &'static str {
    assert!(n <= u16::MAX as usize + 1);
    if n <= (u8::MAX as usize) + 1 {
        "u8"
    } else {
        "u16"
    }
}

/// Generate parser code from a grammar file into an output Rust file.
pub fn generate<P: AsRef<Path>>(grammar_path: P, out_path: P) -> Result<()> {
    let grammar = std::fs::read_to_string(&grammar_path)?;
    let mut context = LexContext::default();
    context.prod_labels.add("start");
    context.nonterms.add("Start");
    let toks = Lexer::tokenize_all(&grammar, &mut context);
    let mut prods = parser::parser().parse(&toks).unwrap();
    prods.insert(
        0,
        Production {
            label: Some(0),
            lhs: 0,
            rhs: vec![Symbol::NonTerm(1)],
        },
    );
    context.terms.add("end");

    let mut tokens = Symtab::new();
    tokens.extend(&context.nonterms);
    tokens.extend(&context.terms);

    let n_nonterms = context.nonterms.len();
    let n_terms = context.terms.len();
    let n_tokens = tokens.len();
    let n_prods = prods.len();

    let prodsv: Vec<_> = prods
        .iter()
        .map(|prod| {
            std::iter::once(prod.lhs)
                .chain(prod.rhs.iter().map(|sym| match sym {
                    Symbol::NonTerm(i) => *i,
                    Symbol::Term(i) => *i + n_nonterms,
                }))
                .collect::<Vec<usize>>()
        })
        .collect();

    let mut out = std::fs::File::create(out_path)?;

    writeln!(out, "/*")?;
    writeln!(out, "Produced by parser generator ASLR")?;
    writeln!(
        out,
        "Copyright (c) 2005-2025 IKH Software, Inc. <support@ikhsoftware.com>"
    )?;
    writeln!(out, "\n")?;

    let tokens_vec = tokens.vec();

    slr::write_prods(&mut out, &prodsv, &tokens_vec)?;
    writeln!(out, "\n")?;

    let c = slr::construct_set(&prodsv, n_nonterms, n_terms);
    let n_states = c.len();
    slr::write_set(&mut out, &c, &prodsv, &tokens_vec)?;

    let (fst, nullable) = slr::first_sets(&prodsv, n_nonterms, n_terms);
    slr::write_fstflw(&mut out, &fst, Some(&nullable), &tokens_vec)?;
    writeln!(out, "")?;

    let flw = slr::follow_sets(&prodsv, n_nonterms, n_terms, 0, &fst, &nullable);
    slr::write_fstflw(&mut out, &flw, None, &tokens_vec)?;
    writeln!(out, "")?;
    writeln!(out, "*/\n")?;

    let tab = slr::construct_slr(&c, &flw, &prodsv, n_nonterms, n_terms);

    let n_ambigs: usize = tab
        .iter()
        .flatten()
        .filter(|actions| actions.len() >= 2)
        .count();

    writeln!(out, "use num_enum::{{IntoPrimitive, TryFromPrimitive}};")?;
    writeln!(out, "")?;
    writeln!(out, "pub const N_TOKENS: usize = {};", n_tokens)?;
    writeln!(out, "pub const N_NONTERMINALS: usize = {};", n_nonterms)?;
    writeln!(out, "pub const N_TERMINALS: usize = {};", n_terms)?;
    writeln!(out, "pub const N_PRODUCTIONS: usize = {};", n_prods)?;
    writeln!(out, "pub const N_STATES: usize = {};", n_states)?;
    writeln!(out, "pub const N_AMBIGS: usize = {};", n_ambigs)?;
    writeln!(out, "")?;

    let prod_labels: Vec<_> = prods
        .iter()
        .enumerate()
        .map(|(i, p)| match p.label {
            Some(j) => context.prod_labels.sym(j).unwrap().to_owned(),
            None => format!("rule{}", i),
        })
        .collect();

    writeln!(
        out,
        "#[derive(Clone, Copy, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]\n#[repr(usize)]\npub enum ProdID {{"
    )?;
    for (i, s) in prod_labels.iter().enumerate() {
        writeln!(out, "   {} = {},", capitalize_first(s), i)?;
    }
    writeln!(out, "}}")?;
    writeln!(out, "")?;

    writeln!(
        out,
        "pub const PRODUCTION_LABELS: [&str; N_PRODUCTIONS] = ["
    )?;
    for (i, s) in prod_labels.iter().enumerate() {
        writeln!(out, "   {:?}, // {}", s, i)?;
    }
    writeln!(out, "];\n")?;

    writeln!(
        out,
        "#[derive(Clone, Copy, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]\n#[repr(usize)]\npub enum TokenID {{"
    )?;
    for (i, s) in tokens.iter().enumerate() {
        if i == 0 {
            writeln!(out, "    // Nonterminals:")?;
        }
        if i == n_nonterms {
            writeln!(out, "\n    // Terminals:")?;
        }
        writeln!(out, "    {} = {},", capitalize_first(s), i,)?;
    }
    writeln!(out, "    {} = {},", "Error", n_tokens)?;
    writeln!(out, "}}")?;
    writeln!(out, "")?;

    writeln!(out, "pub const TOKEN_LABELS: [&str; N_TOKENS + 1] = [")?;
    for (i, s) in tokens.iter().enumerate() {
        writeln!(out, "    {:?}, // {}", s, i)?;
    }
    writeln!(out, "    {:?}, // {}", "error", n_tokens)?;
    writeln!(out, "];\n")?;

    writeln!(out, "#[derive(Clone, Copy, Debug)]\npub struct Prod(")?;
    writeln!(out, "    pub TokenID, // left token")?;
    writeln!(out, "    pub usize, // RHS size")?;
    writeln!(
        out,
        "    pub Option<usize>, // index of rightmost terminal in RHS (if any)"
    )?;
    writeln!(out, ");\n")?;

    writeln!(out, "pub const PRODS: [Prod; N_PRODUCTIONS] = [")?;
    for (i, p) in prods.iter().enumerate() {
        writeln!(
            out,
            "    Prod(TokenID::{}, {}, {:?}), // {}",
            capitalize_first(context.nonterms.sym(p.lhs).unwrap()),
            p.rhs.len(),
            p.rhs.iter().rposition(|s| matches!(s, Symbol::Term(_))),
            i
        )?;
    }
    writeln!(out, "];\n")?;

    writeln!(
        out,
        "#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum Action {{"
    )?;
    writeln!(out, "    Error,")?;
    writeln!(out, "    Accept,")?;
    writeln!(
        out,
        "    Shift({}),",
        calculate_minimum_unsigned_type(n_states)
    )?;
    writeln!(
        out,
        "    Reduce({}),",
        calculate_minimum_unsigned_type(n_prods)
    )?;
    writeln!(
        out,
        "    Ambig({}),",
        calculate_minimum_unsigned_type(n_ambigs)
    )?;
    writeln!(
        out,
        "    Goto({}),",
        calculate_minimum_unsigned_type(n_states)
    )?;
    writeln!(out, "}}\n")?;

    writeln!(out, "pub const TAB: [[Action; N_TOKENS]; N_STATES] = [")?;
    let mut ambig = 0;
    let mut s = String::new();
    for (i, row) in tab.iter().enumerate() {
        writeln!(out, "    /* STATE {} */ [", i)?;
        for (j, actions) in row.iter().enumerate() {
            match actions.len() {
                0 => writeln!(out, "        Action::Error, /* {}({}) */", j, tokens_vec[j],)?,
                1 => {
                    let act = actions.iter().next().unwrap();
                    writeln!(
                        out,
                        "        Action::{}{}, /* {}({}) */",
                        act.typ.to_str(),
                        if act.typ.to_str() == "Accept" {
                            String::new()
                        } else {
                            format!("({})", act.val)
                        },
                        j,
                        tokens_vec[j],
                    )?;
                }
                n => {
                    if n > 2 {
                        writeln!(
                            out,
                            "// ERROR: {} actions (more than 2!) in state {}, token {}({})",
                            n, i, j, tokens_vec[j]
                        )?;
                    }
                    writeln!(
                        out,
                        "        Action::Ambig({}), /* {}({}) */",
                        ambig, j, tokens_vec[j],
                    )?;
                    s.push_str("    [");
                    for act in actions {
                        s.push_str(&format!("Action::{}({}),", act.typ.to_str(), act.val));
                    }
                    s.push_str(&format!("], /* {}, {}({}) */\n", i, j, tokens_vec[j]));
                    ambig += 1;
                }
            }
        }
        writeln!(out, "    ],")?;
    }
    writeln!(out, "];\n")?;

    writeln!(out, "pub const AMBIGS: [[Action; 2]; N_AMBIGS] = [")?;
    write!(out, "{}", s)?;
    writeln!(out, "];\n")?;

    Ok(())
}
