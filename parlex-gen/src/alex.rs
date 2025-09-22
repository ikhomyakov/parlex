use anyhow::{Context, Result, anyhow, bail};
use once_cell::sync::Lazy;
use regex::{Captures, Regex};
use regex_automata::{
    MatchKind,
    dfa::{StartKind, dense},
    nfa::thompson::{Config as ThomConfig, NFA},
    util::syntax,
};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::Path;

#[derive(Debug, Clone)]
struct LRegex {
    label: String,
    regex: String, // after variable substitution
}

#[derive(Debug, Clone)]
struct LexRule {
    label: String,
    modes: Vec<String>,
    regex: String, // after variable substitution
    line_no: usize,
}

#[derive(Debug, Default)]
struct Parsed {
    vars: HashMap<String, String>, // raw values from var defs
    rules: Vec<LexRule>,           // regex is expanded
}

static VAR_DEF_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r#"^([A-Za-z_]+)\s*=\s*(.*)$"#).unwrap());

static LEX_RULE_RE: Lazy<Regex> =
    Lazy::new(|| Regex::new(r#"^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*<([^>]*)>\s*(.+)$"#).unwrap());

static VAR_IN_REGEX_RE: Lazy<Regex> =
    Lazy::new(|| Regex::new(r#"\{\{\s*([A-Za-z_][A-Za-z0-9_]*)\s*\}\}"#).unwrap());

/// Generate lexer code from a spec file into an output Rust file.
pub fn generate<P: AsRef<Path>>(
    spec_path: P,
    out_rs_path: P,
    out_dfale_path: P,
    out_dfabe_path: P,
) -> Result<()> {
    let spec = std::fs::read_to_string(&spec_path)?;
    let (rules, modes, _vars) = parse_alex(&spec)?;

    let mut rule_vecs: HashMap<String, Vec<LRegex>> =
        modes.iter().cloned().map(|key| (key, Vec::new())).collect();

    for r in &rules {
        for m in &r.modes {
            if m == "*" {
                for m in modes.iter() {
                    rule_vecs
                        .get_mut(m)
                        .ok_or(anyhow!("Missing mode {:?}", m))?
                        .push(LRegex {
                            label: r.label.clone(),
                            regex: r.regex.clone(),
                        });
                }
            } else {
                rule_vecs
                    .get_mut(m)
                    .ok_or(anyhow!("Missing mode {:?}", m))?
                    .push(LRegex {
                        label: r.label.clone(),
                        regex: r.regex.clone(),
                    });
            }
        }
    }

    let mut out = std::fs::File::create(out_rs_path)?;

    writeln!(out, "/*")?;
    writeln!(out, "Produced by lexer generator ALEX")?;
    writeln!(
        out,
        "Copyright (c) 2005-2025 IKH Software, Inc. <support@ikhsoftware.com>"
    )?;
    writeln!(out, "*/\n")?;
    writeln!(out, "use include_bytes_aligned::include_bytes_aligned;")?;
    writeln!(out, "")?;

    let mut modes: Vec<_> = modes.iter().filter(|&s| s != "*").collect();
    modes.sort();

    writeln!(out, "pub const N_MODES: usize = {};", modes.len())?;
    writeln!(out, "pub const N_RULES: usize = {};", rules.len() + 2)?;
    writeln!(out, "")?;

    writeln!(
        out,
        "#[derive(Debug, Clone, Copy, PartialEq)]\npub enum Mode {{"
    )?;
    for (i, m) in modes.iter().enumerate() {
        writeln!(out, "    {} = {},", m, i)?;
    }
    writeln!(out, "}}\n")?;

    writeln!(
        out,
        "#[derive(Debug, Clone, Copy, PartialEq)]\npub enum Rule {{"
    )?;
    writeln!(out, "    Empty = 0,")?;
    for (i, r) in rules.iter().enumerate() {
        writeln!(
            out,
            "    {} = {}, // <{}> {}",
            r.label,
            i + 1,
            r.modes.join(","),
            r.regex
        )?;
    }
    writeln!(out, "    End = {},", rules.len() + 1)?;
    writeln!(out, "}}\n")?;

    let max_mode_rules = rule_vecs.values().map(|v| v.len()).max().unwrap_or(0);

    writeln!(
        out,
        "pub const TAB: [[Rule; {}]; {}] = [",
        max_mode_rules,
        modes.len()
    )?;
    for (i, m) in modes.iter().enumerate() {
        writeln!(out, "    /* MODE {} {:?} */ [", i, m)?;
        let rules = rule_vecs.get(*m).ok_or(anyhow!("Missing mode {:?}", m))?;
        for (_j, r) in rules.iter().enumerate() {
            writeln!(out, "        Rule::{},", r.label)?;
        }
        for _ in rules.len()..max_mode_rules {
            writeln!(out, "        Rule::Empty,")?;
        }
        writeln!(out, "    ],")?;
    }
    writeln!(out, "];\n")?;

    let mut file_le = std::fs::File::create(out_dfale_path)?;
    let mut file_be = std::fs::File::create(out_dfabe_path)?;

    writeln!(out, "#[cfg(target_endian = \"little\")]")?;
    writeln!(
        out,
        "pub static DFA_BYTES: &[u8] = include_bytes_aligned!(4, \"dfa.le.bin\");"
    )?;
    writeln!(out, "#[cfg(target_endian = \"big\")]")?;
    writeln!(
        out,
        "pub static DFA_BYTES: &[u8] = include_bytes_aligned!(4, \"dfa.be.bin\");"
    )?;
    writeln!(out, "")?;

    let mut offset = 0;
    writeln!(out, "pub const DFA_OFFSETS: [usize; {}] = [", modes.len())?;

    for (_i, m) in modes.iter().enumerate() {
        let rules = rule_vecs.get(*m).ok_or(anyhow!("Missing mode {:?}", m))?;
        let mut hirs = Vec::new();
        let conf = syntax::Config::new().utf8(false);
        for (_j, r) in rules.iter().enumerate() {
            hirs.push(syntax::parse_with(&r.regex, &conf).with_context(|| {
                format!(
                    "Failed to parse regex {} for mode {:?} rule {:?}",
                    r.regex, m, r.label
                )
            })?);
        }

        let nfa = NFA::compiler()
            .configure(ThomConfig::new().utf8(false))
            .build_many_from_hir(&hirs)?;
        let dfa = dense::Builder::new()
            .configure(
                dense::DFA::config()
                    .match_kind(MatchKind::All)
                    .start_kind(StartKind::Anchored),
            )
            .build_from_nfa(&nfa)?;

        let (bytes, pad) = dfa.to_bytes_little_endian();
        assert!((bytes.len() - pad) % 4 == 0);
        file_le.write_all(&bytes[pad..])?;

        let (bytes, pad) = dfa.to_bytes_big_endian();
        assert!((bytes.len() - pad) % 4 == 0);
        file_be.write_all(&bytes[pad..])?;

        writeln!(out, "    {}, // {}", offset, m)?;
        offset += bytes.len() - pad;
    }
    writeln!(out, "];\n")?;

    Ok(())
}

fn parse_alex(input: &str) -> Result<(Vec<LexRule>, HashSet<String>, HashMap<String, String>)> {
    let mut rules: Vec<LexRule> = Vec::new();
    let mut modes: HashSet<String> = HashSet::new();
    let mut vars: HashMap<String, String> = HashMap::new();

    for (i, raw_line) in input.lines().enumerate() {
        let line_no = i + 1;
        let line = raw_line.trim();

        if line.is_empty() || line.starts_with("--") {
            continue;
        }

        if let Some(cap) = VAR_DEF_RE.captures(line) {
            let name = cap[1].to_string();
            let value = expand_vars(cap[2].trim(), &vars)?;
            vars.insert(name, value);
            continue;
        }

        if let Some(cap) = LEX_RULE_RE.captures(line) {
            let label = cap[1].to_string();
            let modes_str = cap[2].trim();
            let regex = expand_vars(cap[3].trim(), &vars)?;

            let rule_modes: Vec<String> = modes_str
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();

            modes.extend(rule_modes.iter().cloned());

            if rule_modes.is_empty() {
                bail!("No modes found at line ({}): {:?}", line_no, line);
            }

            rules.push(LexRule {
                label,
                modes: rule_modes,
                regex,
                line_no,
            });
            continue;
        }

        bail!("Unrecognized line ({}): {:?}", line_no, line);
    }

    Ok((rules, modes, vars))
}

fn expand_vars(input: &str, vars: &HashMap<String, String>) -> Result<String> {
    let mut out = input.to_string();
    let mut seen_any = true;
    let mut depth = 0;

    while seen_any {
        depth += 1;
        if depth > 64 {
            bail!(
                "Variable expansion exceeded depth (possible cycle): {}",
                input
            );
        }

        seen_any = false;
        let mut missing: HashSet<String> = HashSet::new();

        out = VAR_IN_REGEX_RE
            .replace_all(&out, |caps: &Captures| {
                let name = caps[1].to_string();
                if let Some(val) = vars.get(&name) {
                    seen_any = true;
                    format!("(?:{})", val)
                } else {
                    missing.insert(name.clone());
                    caps.get(0).unwrap().as_str().to_string()
                }
            })
            .to_string();

        if !missing.is_empty() {
            let list = missing.into_iter().collect::<Vec<_>>().join(", ");
            bail!("Unknown variable(s): {}", list);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_example() {
        let input = r#"
SPACE = (?-u:[ \t\f])
ATOM = (?-u:([a-z]([a-z]|[A-Z_]|[0-9])*)|[-~@#$^&*+=<>:.?/!;]+)
VAR = (?-u:[A-Z_]([a-z]|[A-Z_]|[0-9])*)
HEX_CONST = (?-u:0x[0-9a-fA-F]*)
OCT_CONST = (?-u:0[0-7]*)
DEC_CONST = (?-u:[1-9][0-9]*)
FP_CONST = (?-u:([0-9]*\.[0-9]+([eE][+-]?[0-9]+)?)|([0-9]+\.[0-9]*([eE][+-]?[0-9]+)?))
LABEL = (?-u:[a-z]([a-z]|[A-Z_]|[0-9])*)
NEW_LINE = (?-u:(\r?\n))

Expr1: <Expr> %.*
Expr2: <Expr, Comment> (?-u:/\*)
Comment1: <Comment> (?-u:\*/)
Comment2: <Comment> [^*\r\n]
Expr3: <Expr> {{SPACE}}
Expr4: <Expr, Comment> {{NEW_LINE}}
Comment3: <Comment> .
Expr5: <Expr> (?-u:\()
Expr6: <Expr> (?-u:\))
Expr7: <Expr> (?-u:\[)

"#;

        let (rules, modes, vars) = parse_alex(input).unwrap();
        assert!(vars.contains_key("SPACE"));
        assert_eq!(rules.len(), 10);

        let r = rules.iter().find(|r| r.label == "Expr3").unwrap();
        assert!(r.regex.starts_with("(?:"));
        assert!(r.modes.contains(&"Expr".to_string()));
    }
}
