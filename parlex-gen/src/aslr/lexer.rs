use super::symtab::Symtab;
use logos::Logos;
use std::collections::HashMap;

#[derive(Default, Debug)]
pub struct LexContext {
    pub terms: Symtab,
    pub nonterms: Symtab,
    pub prod_labels: Symtab,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    ProdLabel(usize),
    NonTerm(usize),
    Prod,
    Term(usize),
    LineFeed,
}

#[derive(Logos, Debug, PartialEq)]
#[logos(skip r"[ \t\f]+")]
enum LogosToken {
    #[regex(r"[\n]")]
    LineFeed,
    #[regex(r"--[^\n]*")]
    Comment,
    #[regex(r"->")]
    Prod,
    #[regex(r"[a-z]([a-zA-Z0-9])*:")]
    ProdLabel,
    #[regex(r"[a-z]([a-zA-Z0-9])*")]
    Atom,
    #[regex(r"[A-Z][a-zA-Z0-9]*")]
    Var,
    #[regex(r###"[-~`!@#$%^&*+=|\\<>?/;\(\)\[\]{},\.'":]"###)]
    Sym,
}

pub const SYM_NAMES: &[(char, &str)] = &[
    ('.', "dot"),
    ('-', "minus"),
    ('~', "tilde"),
    ('`', "backtick"),
    ('!', "exclamation"),
    ('@', "at"),
    ('#', "hash"),
    ('$', "dollar"),
    ('%', "percent"),
    ('^', "caret"),
    ('&', "ampersand"),
    ('*', "asterisk"),
    ('+', "plus"),
    ('=', "equals"),
    ('|', "pipe"),
    ('\\', "backslash"),
    ('<', "lessThan"),
    ('>', "greaterThan"),
    ('?', "question"),
    ('/', "slash"),
    (';', "semicolon"),
    ('(', "leftParen"),
    (')', "rightParen"),
    ('[', "leftBrack"),
    (']', "rightBrack"),
    ('{', "leftBrace"),
    ('}', "rightBrace"),
    (',', "comma"),
    ('\'', "singleQuote"),
    ('"', "doubleQuote"),
    (':', "colon"),
];

pub struct Lexer<'source> {
    inner: logos::Lexer<'source, LogosToken>,
    sym_names: HashMap<char, &'static str>,
}

impl<'source> Lexer<'source> {
    pub fn new(input: &'source str) -> Self {
        Self {
            inner: LogosToken::lexer(input),
            sym_names: SYM_NAMES.iter().cloned().collect(),
        }
    }

    pub fn next_token(&mut self, ctx: &mut LexContext) -> Option<Token> {
        while let Some(kind) = self.inner.next() {
            let slice = self.inner.slice();
            return match kind {
                Ok(token) => match token {
                    LogosToken::Sym => {
                        let name = if let Some(first_char) = slice.chars().next() {
                            if let Some(name) = self.sym_names.get(&first_char) {
                                name
                            } else {
                                unreachable!();
                            }
                        } else {
                            unreachable!();
                        };
                        Some(Token::Term(ctx.terms.add(name)))
                    }
                    LogosToken::Atom => Some(Token::Term(ctx.terms.add(slice))),
                    LogosToken::Var => Some(Token::NonTerm(ctx.nonterms.add(slice))),
                    LogosToken::ProdLabel => {
                        let slice = match slice.char_indices().next_back() {
                            Some((idx, _)) => &slice[..idx],
                            None => "",
                        };
                        Some(Token::ProdLabel(ctx.prod_labels.add(slice)))
                    }
                    LogosToken::Prod => Some(Token::Prod),
                    LogosToken::Comment => continue,
                    LogosToken::LineFeed => Some(Token::LineFeed),
                },
                Err(err) => {
                    panic!("Lexer error: {err:?}");
                }
            };
        }
        None
    }

    pub fn tokenize_all(input: &'source str, ctx: &mut LexContext) -> Vec<Token> {
        let mut lex = Lexer::new(input);
        let mut out = Vec::new();
        while let Some(tok) = lex.next_token(ctx) {
            out.push(tok);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_terms() {
        let mut ctx = LexContext::default();
        let input = "\n\n\nfoo: XYZ -> +& () bar x123 ABC -- hello\n";
        let toks = Lexer::tokenize_all(input, &mut ctx);
        assert!(toks.len() == 14);
    }
}
