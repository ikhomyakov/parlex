use crate::oper::{Assoc, Fixity, OperArg, OperDef, OperDefs};
use crate::parser::TokenID;
use anyhow::{Error, Result, anyhow, bail};
use arena_terms::{Arena, Term, View};
use chrono::{DateTime, FixedOffset, Utc};
use smartstring::alias::String;
use std::io::{self, BufReader, Read};
use std::iter::FusedIterator;
use std::mem;

include!(concat!(env!("OUT_DIR"), "/lexer_data.rs"));

#[derive(Debug, Clone, Default)]
pub enum Value {
    #[default]
    None,
    Term(Term),
    Index(usize),
}

macro_rules! impl_tryfrom_value {
    ( $( $Variant:ident => $ty:ty ),+ $(,)? ) => {
        $(
            impl ::core::convert::TryFrom<Value> for $ty {
                type Error = ::anyhow::Error;
                fn try_from(v: Value) -> ::anyhow::Result<Self> {
                    match v {
                        Value::$Variant(x) => Ok(x),
                        _ => ::anyhow::bail!(
                            "invalid value: expected {}",
                            stringify!($Variant),
                        ),
                    }
                }
            }
        )+
    };
}

impl_tryfrom_value! {
    Term => Term,
    Index => usize,
}

#[derive(Debug, Clone)]
pub struct TermToken {
    pub token_id: TokenID,
    pub value: Value,
    pub line_no: usize,
    pub op_tab_index: Option<usize>,
}

impl TermToken {
    #[must_use]
    pub fn new(token_id: TokenID, value: Value, line_no: usize) -> Self {
        Self {
            token_id,
            value,
            line_no,
            op_tab_index: None,
        }
    }
}

impl Token for TermToken {
    type TokenID = TokenID;

    fn token_id(&self) -> Self::TokenID {
        self.token_id
    }
    fn line_no(&self) -> usize {
        self.line_no
    }
}

fn parse_date_to_epoch(s: &str, fmt: Option<&str>) -> Result<i64> {
    let dt_fixed: DateTime<FixedOffset> = match fmt {
        None => DateTime::parse_from_rfc3339(s)?,
        Some(layout) => DateTime::parse_from_str(s, layout)?,
    };
    let dt_utc = dt_fixed.with_timezone(&Utc);
    Ok(dt_utc.timestamp_millis())
}

fn parse_i64(s: &str, base: u32) -> Result<i64> {
    if s.is_empty() {
        return Ok(0);
    }
    match u64::from_str_radix(s, base) {
        Ok(n) => Ok(n.try_into()?),
        Err(e) if e.kind() == &std::num::IntErrorKind::InvalidDigit => {
            bail!("digit not valid for base")
        }
        Err(_) => bail!("number overflowed u64"),
    }
}

pub struct TermLexer<I>
where
    I: FusedIterator<Item = u8>,
{
    ctx: LexerCtx<I, <Self as Lexer<Arena>>::LexerData, <Self as Lexer<Arena>>::Token>,
    pub opers: OperDefs,
    nest_count: isize,
    comment_nest_count: isize,
    curly_nest_count: isize,
    script_curly_nest_count: isize,
    bin_count: isize,
    bin_label: Vec<u8>,
}

impl<I> TermLexer<I>
where
    I: FusedIterator<Item = u8>,
{
    pub fn try_new(input: I, opers: Option<OperDefs>) -> Result<Self> {
        Ok(Self {
            ctx: LexerCtx::try_new(input)?,
            opers: match opers {
                Some(opers) => opers,
                None => OperDefs::new(),
            },
            nest_count: 0,
            comment_nest_count: 0,
            curly_nest_count: 0,
            script_curly_nest_count: 0,
            bin_count: 0,
            bin_label: Vec::new(),
        })
    }

    fn yield_id(&mut self, token_id: TokenID) {
        //self.clear();
        self.yield_token(TermToken {
            token_id,
            value: Value::None,
            line_no: self.ctx().line_no,
            op_tab_index: None,
        });
    }

    fn yield_term(&mut self, token_id: TokenID, term: Term) {
        self.yield_token(TermToken {
            token_id,
            value: Value::Term(term),
            line_no: self.ctx().line_no,
            op_tab_index: None,
        });
    }

    fn yield_index(&mut self, token_id: TokenID, index: usize) {
        self.yield_token(TermToken {
            token_id,
            value: Value::Index(index),
            line_no: self.ctx().line_no,
            op_tab_index: None,
        });
    }

    fn yield_optab(&mut self, token_id: TokenID, term: Term, op_tab_index: Option<usize>) {
        self.yield_token(TermToken {
            token_id,
            value: Value::Term(term),
            line_no: self.ctx().line_no,
            op_tab_index,
        });
    }
}

impl<I> Lexer<Arena> for TermLexer<I>
where
    I: FusedIterator<Item = u8>,
{
    type Input = I;
    type LexerData = LexData;
    type Token = TermToken;

    fn ctx(&self) -> &LexerCtx<Self::Input, Self::LexerData, Self::Token> {
        &self.ctx
    }

    fn ctx_mut(&mut self) -> &mut LexerCtx<Self::Input, Self::LexerData, Self::Token> {
        &mut self.ctx
    }

    fn action(
        &mut self,
        arena: &mut Arena,
        rule: <Self::LexerData as LexerData>::LexerRule,
    ) -> Result<()> {
        log::trace!(
            "ACTION begin: rule {:?}, buf {:?}, buf2 {:?}, label{:?}",
            rule,
            str::from_utf8(&self.ctx().buffer),
            str::from_utf8(&self.ctx().buffer2),
            str::from_utf8(&self.bin_label),
        );
        match rule {
            Rule::Empty => {
                unreachable!()
            }
            Rule::LineComment => {}
            Rule::CommentStart => {
                if self.comment_nest_count == 0 {
                    self.begin(Mode::Comment);
                }
                self.comment_nest_count += 1;
            }
            Rule::CommentEnd => {
                self.comment_nest_count -= 1;
                if self.comment_nest_count == 0 {
                    self.begin(Mode::Expr);
                }
            }
            Rule::CommentChar | Rule::ExprSpace | Rule::CommentAnyChar => {}
            Rule::ExprNewLine | Rule::CommentNewLine => {
                self.ctx_mut().line_no += 1;
            }
            Rule::LeftParen => {
                self.nest_count += 1;
                self.yield_id(TokenID::LeftParen);
            }
            Rule::RightParen => {
                self.nest_count -= 1;
                self.yield_id(TokenID::RightParen);
            }
            Rule::LeftBrack => {
                self.nest_count += 1;
                self.yield_id(TokenID::LeftBrack);
            }
            Rule::RightBrack => {
                self.nest_count -= 1;
                self.yield_id(TokenID::RightBrack);
            }
            Rule::Comma => {
                self.yield_id(TokenID::Comma);
            }
            Rule::Pipe => {
                self.yield_id(TokenID::Pipe);
            }
            Rule::RightBrace => {
                self.nest_count -= 1;
                self.curly_nest_count -= 1;
                if self.curly_nest_count >= 0 {
                    self.begin(Mode::Str);
                    self.yield_id(TokenID::RightParen);
                    self.yield_term(TokenID::Atom, arena.atom("++"));
                } else {
                    self.yield_term(TokenID::Error, arena.str("}"));
                }
                self.clear();
            }
            Rule::Func => {
                self.nest_count += 1;
                self.ctx_mut().buffer.pop();
                let s = self.take_str()?;
                let op_tab_idx = self.opers.lookup(&s);
                let op_tab = self.opers.get(op_tab_idx);

                let atom = arena.atom(s);

                if op_tab.is_oper() {
                    let (has_empty, has_non_empty) =
                        [Fixity::Prefix, Fixity::Infix, Fixity::Postfix]
                            .iter()
                            .filter_map(|f| {
                                op_tab
                                    .get_op_def(*f)
                                    .map(|x| x.args.len() <= OperDef::required_arity(*f))
                            })
                            .fold((false, false), |(e, ne), is_empty| {
                                if is_empty { (true, ne) } else { (e, true) }
                            });

                    match (has_empty, has_non_empty) {
                        (false, false) => unreachable!(),
                        (true, false) => {
                            self.yield_optab(TokenID::AtomOper, atom, op_tab_idx);
                            self.yield_id(TokenID::LeftParen);
                        }
                        (false, true) => {
                            self.yield_optab(TokenID::FuncOper, atom, op_tab_idx);
                        }
                        (true, true) => bail!("arguments conflict in op defs for {:?}", atom),
                    }
                } else {
                    self.yield_optab(TokenID::Func, atom, op_tab_idx);
                }
            }
            Rule::Var => {
                let s = self.take_str()?;
                self.yield_term(TokenID::Var, arena.var(s));
            }
            Rule::Atom => {
                if self.ctx().buffer == b"." && self.nest_count == 0 {
                    self.yield_id(TokenID::Dot);
                    self.yield_id(TokenID::End);
                } else {
                    let s = self.take_str()?;
                    let op_tab_idx = self.opers.lookup(&s);
                    let op_tab = self.opers.get(op_tab_idx);
                    let atom = arena.atom(s);
                    if op_tab.is_oper() {
                        self.yield_optab(TokenID::AtomOper, atom, op_tab_idx);
                    } else {
                        self.yield_optab(TokenID::Atom, atom, op_tab_idx);
                    }
                }
            }
            Rule::Date => {
                self.ctx_mut().buffer.pop();
                self.ctx_mut().buffer.drain(0..5);
                let s = self.take_str()?;
                let d = parse_date_to_epoch(s.as_str(), None)?;
                self.yield_term(TokenID::Date, arena.date(d));
            }
            Rule::Hex => {
                self.begin(Mode::Hex);
                self.ctx_mut().buffer2.clear();
            }
            Rule::HexSpace => {}
            Rule::HexNewLine => {
                self.ctx_mut().line_no += 1;
            }
            Rule::HexByte => {
                let s = str::from_utf8(&self.ctx().buffer)?;
                match u8::from_str_radix(s, 16) {
                    Ok(b) => {
                        self.ctx_mut().buffer2.push(b);
                    }
                    Err(_) => {
                        self.yield_term(TokenID::Error, arena.str(s));
                    }
                }
            }
            Rule::HexRightBrace => {
                self.ctx_mut().buffer.pop();
                let bytes = self.take_bytes2();
                self.yield_term(TokenID::Bin, arena.bin(bytes));
                self.begin(Mode::Expr);
            }
            Rule::Bin => {
                self.begin(Mode::Bin);
            }
            Rule::Text => {
                self.begin(Mode::Text);
            }
            Rule::BinSpace | Rule::TextSpace => {}
            Rule::BinNewLine | Rule::TextNewLine => {
                self.ctx_mut().line_no += 1;
            }
            r @ (Rule::BinCount | Rule::TextCount) => {
                let s = str::from_utf8(&self.ctx().buffer)?;
                let mut s = String::from(s.trim());
                if &s[s.len() - 1..] == "\n" {
                    self.ctx_mut().line_no += 1;
                }
                if &s[s.len() - 1..] == ":" {
                    s.pop();
                }
                self.bin_count = s.parse()?;
                if self.bin_count > 0 {
                    if r == Rule::BinCount {
                        self.begin(Mode::BinCount);
                    } else {
                        self.begin(Mode::TextCount);
                    }
                    self.clear();
                    self.accum();
                }
            }
            r @ (Rule::BinCountAnyChar | Rule::TextCountAnyChar) => {
                self.bin_count -= 1;
                if self.bin_count == 0 {
                    self.extend_buffer2_with_buffer();
                    self.clear();
                    if r == Rule::BinCountAnyChar {
                        self.begin(Mode::Bin);
                    } else {
                        self.begin(Mode::Text);
                    }
                }
            }
            r @ (Rule::BinCountNLChar | Rule::TextCountNewLine) => {
                self.ctx_mut().line_no += 1;
                if self.ctx_mut().buffer[0] == b'\r' {
                    self.ctx_mut().buffer.remove(0);
                }
                self.bin_count -= 1;
                if self.bin_count == 0 {
                    self.extend_buffer2_with_buffer();
                    self.clear();
                    if r == Rule::BinCountNLChar {
                        self.begin(Mode::Bin);
                    } else {
                        self.begin(Mode::Text);
                    }
                }
            }
            r @ (Rule::BinRightBrace | Rule::TextRightBrace) => {
                if r == Rule::BinRightBrace {
                    let bytes = self.take_bytes2();
                    self.yield_term(TokenID::Bin, arena.bin(bytes));
                } else {
                    let s = self.take_str2()?;
                    self.yield_term(TokenID::Str, arena.str(s));
                }
                self.begin(Mode::Expr);
            }
            r @ (Rule::BinLabelStart | Rule::TextLabelStart) => {
                self.bin_label.clear();
                let len = self.ctx().buffer.len();
                if self.ctx_mut().buffer[len - 1] == b'\n' {
                    self.ctx_mut().line_no += 1;
                    self.bin_label.push(b'\n');
                    self.ctx_mut().buffer.pop();
                    let len = self.ctx().buffer.len();
                    if self.ctx_mut().buffer[len - 1] == b'\r' {
                        self.bin_label.insert(0, b'\r');
                        self.ctx_mut().buffer.pop();
                    }
                } else {
                    let len = self.ctx().buffer.len();
                    let b = self.ctx().buffer[len - 1];
                    self.bin_label.push(b);
                    self.ctx_mut().buffer.pop();
                }

                let buf = mem::take(&mut self.ctx_mut().buffer);
                self.bin_label.extend(buf);

                if r == Rule::BinLabelStart {
                    self.begin(Mode::BinLabel);
                } else {
                    self.begin(Mode::TextLabel);
                }
            }
            r @ (Rule::BinLabelEnd | Rule::TextLabelEnd) => {
                if self.ctx_mut().buffer[0] != b':' {
                    self.ctx_mut().line_no += 1;
                }
                if self.ctx().buffer == self.bin_label {
                    if r == Rule::BinLabelEnd {
                        self.begin(Mode::Bin);
                    } else {
                        self.begin(Mode::Text);
                    }
                } else {
                    if r == Rule::TextLabelEnd && self.ctx_mut().buffer[0] == b'\r' {
                        self.ctx_mut().buffer.remove(0);
                    }
                    self.extend_buffer2_with_buffer();
                }
            }
            r @ (Rule::BinLabelNLChar | Rule::TextLabelNewLine) => {
                self.ctx_mut().line_no += 1;
                if r == Rule::TextLabelNewLine && self.ctx_mut().buffer[0] == b'\r' {
                    self.ctx_mut().buffer.remove(0);
                }
                self.extend_buffer2_with_buffer();
            }
            Rule::BinLabelAnyChar | Rule::TextLabelAnyChar => {
                self.extend_buffer2_with_buffer();
            }
            Rule::LeftBrace => {
                self.begin(Mode::Script);
                self.clear();
                self.accum();
            }
            Rule::ScriptNotBraces => {}
            Rule::ScriptLeftBrace => {
                self.script_curly_nest_count += 1;
            }
            Rule::ScriptRightBrace => {
                if self.script_curly_nest_count != 0 {
                    self.script_curly_nest_count -= 1;
                } else {
                    self.ctx_mut().buffer.pop();
                    let s = self.take_str()?;
                    self.yield_term(TokenID::Str, arena.str(s));
                    self.begin(Mode::Expr);
                }
            }
            Rule::ScriptNewLine => {
                self.ctx_mut().line_no += 1;
            }
            Rule::HexConst => {
                self.ctx_mut().buffer.drain(0..2);
                let s = self.take_str()?;
                let val = parse_i64(s.as_str(), 16)?;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::BaseConst => {
                let s = self.take_str()?;
                let (base_str, digits) =
                    s.split_once('\'').ok_or(anyhow!("missing ' separator"))?;
                let base: u32 = base_str.parse().map_err(|_| anyhow!("invalid base"))?;
                let val = parse_i64(digits, base)?;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::CharHex => {
                let mut s = self.take_str()?;
                s.drain(0..4);
                let val = parse_i64(s.as_str(), 16)?;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::CharOct => {
                let mut s = self.take_str()?;
                s.drain(0..3);
                let val = parse_i64(s.as_str(), 8)?;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::CharNewLine1 | Rule::CharNewLine2 | Rule::CharNewLine4 => {
                self.ctx_mut().line_no += 1;
                self.yield_term(TokenID::Int, arena.int('\n' as i64));
            }
            Rule::CharNotBackslash => {
                let mut s = self.take_str()?;
                s.drain(0..2);
                let val = s.chars().next().ok_or(anyhow!("invalid char"))? as i64;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::CharCtrl => {
                let mut s = self.take_str()?;
                s.drain(0..4);
                let val = s.chars().next().ok_or(anyhow!("invalid char"))? as i64 - '@' as i64;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::CharDel1 | Rule::CharDel2 => {
                self.yield_term(TokenID::Int, arena.int('\x7F' as i64));
            }
            Rule::CharEsc => {
                self.yield_term(TokenID::Int, arena.int('\x1B' as i64));
            }
            Rule::CharBell => {
                self.yield_term(TokenID::Int, arena.int('\u{0007}' as i64));
            }
            Rule::CharBackspace => {
                self.yield_term(TokenID::Int, arena.int('\u{0008}' as i64));
            }
            Rule::CharFormFeed => {
                self.yield_term(TokenID::Int, arena.int('\u{000C}' as i64));
            }
            Rule::CharNewLine3 => {
                self.yield_term(TokenID::Int, arena.int('\n' as i64));
            }
            Rule::CharCarriageReturn => {
                self.yield_term(TokenID::Int, arena.int('\r' as i64));
            }
            Rule::CharTab => {
                self.yield_term(TokenID::Int, arena.int('\t' as i64));
            }
            Rule::CharVerticalTab => {
                self.yield_term(TokenID::Int, arena.int('\u{000B}' as i64));
            }
            Rule::CharAny => {
                let mut s = self.take_str()?;
                s.drain(0..3);
                let val = s.chars().next().ok_or(anyhow!("invalid char"))? as i64;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::OctConst => {
                let s = self.take_str()?;
                let val = parse_i64(s.as_str(), 8)?;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::DecConst => {
                let s = self.take_str()?;
                let val = parse_i64(s.as_str(), 10)?;
                self.yield_term(TokenID::Int, arena.int(val));
            }
            Rule::FPConst => {
                let s = self.take_str()?;
                let val: f64 = s.parse()?;
                self.yield_term(TokenID::Real, arena.real(val));
            }
            Rule::DoubleQuote => {
                self.begin(Mode::Str);
                self.clear();
                self.accum();
            }
            Rule::SingleQuote => {
                self.begin(Mode::Atom);
                self.clear();
                self.accum();
            }
            Rule::StrAtomCharHex => {
                let len = self.ctx().buffer.len();
                let b: u8 = parse_i64(str::from_utf8(&self.ctx_mut().buffer[len - 2..])?, 16)?
                    .try_into()?;
                self.ctx_mut().buffer.truncate(len - 4);
                self.ctx_mut().buffer.push(b);
            }
            Rule::StrAtomCharOct => {
                let slash_pos = self.ctx().buffer.iter().rposition(|&b| b == b'\\').unwrap();
                let b: u8 = parse_i64(str::from_utf8(&self.ctx().buffer[slash_pos + 1..])?, 8)?
                    .try_into()?;
                self.ctx_mut().buffer.truncate(slash_pos);
                self.ctx_mut().buffer.push(b);
            }
            Rule::StrAtomCharCtrl => {
                let len = self.ctx().buffer.len();
                let b = self.ctx_mut().buffer[len - 1] - b'@';
                self.ctx_mut().buffer.truncate(len - 3);
                self.ctx_mut().buffer.push(b);
            }
            Rule::StrAtomCharDel1 => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\x7F');
            }
            Rule::StrAtomCharDel2 => {
                let idx = self.ctx().buffer.len() - 3;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\x7F');
            }
            Rule::StrAtomCharEsc => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\x1B');
            }
            Rule::StrAtomCharBell => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\x07');
            }
            Rule::StrAtomCharBackspace => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\x08');
            }
            Rule::StrAtomCharFormFeed => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\x0C');
            }
            Rule::StrAtomCharNewLine => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\n');
            }
            Rule::StrAtomCharCarriageReturn => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\r');
            }
            Rule::StrAtomCharTab => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\t');
            }
            Rule::StrAtomVerticalTab => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.truncate(idx);
                self.ctx_mut().buffer.push(b'\x0B');
            }
            Rule::StrAtomCharSkipNewLine => {
                self.ctx_mut().line_no += 1;
                self.ctx_mut().buffer.pop();
                let idx = self.ctx().buffer.len() - 1;
                if self.ctx_mut().buffer[idx] == b'\r' {
                    self.ctx_mut().buffer.pop();
                }
                self.ctx_mut().buffer.pop();
            }
            Rule::StrAtomCharAny | Rule::StrAtomCharBackslash => {
                let idx = self.ctx().buffer.len() - 2;
                self.ctx_mut().buffer.remove(idx);
            }
            Rule::StrChar | Rule::AtomChar | Rule::StrAtomCarriageReturn => {}
            Rule::StrDoubleQuote => {
                self.begin(Mode::Expr);
                self.ctx_mut().buffer.pop();
                let s = self.take_str()?;
                self.yield_term(TokenID::Str, arena.str(s));
            }
            Rule::AtomSingleQuote => {
                self.begin(Mode::Expr);
                self.ctx_mut().buffer.pop();
                let s = self.take_str()?;
                self.yield_term(TokenID::Atom, arena.atom(s));
            }
            Rule::AtomLeftParen => {
                self.begin(Mode::Expr);
                self.nest_count += 1;
                let mut s = self.take_str()?;
                s.truncate(s.len() - 2);
                self.yield_term(TokenID::Func, arena.atom(s));
            }
            Rule::AtomLeftBrace => {}
            Rule::StrLeftBrace => {
                self.begin(Mode::Expr);
                self.nest_count += 1;
                self.curly_nest_count += 1;
                let mut s = self.take_str()?;
                s.pop();
                self.yield_term(TokenID::Str, arena.str(s));
                self.yield_term(TokenID::Atom, arena.atom("++"));
                self.yield_id(TokenID::LeftParen);
            }
            Rule::StrAtomNewLine => {
                self.ctx_mut().line_no += 1;
            }
            Rule::Error => {
                let s = self.take_str()?;
                self.yield_term(TokenID::Error, arena.str(s));
            }
            Rule::End => {
                if self.ctx().mode == Mode::Expr {
                    self.yield_id(TokenID::End);
                } else {
                    self.yield_term(TokenID::Error, arena.str("<END>"));
                }
            }
        }

        log::trace!(
            "ACTION end: rule {:?}, buf {:?}, buf2 {:?}, label{:?}",
            rule,
            str::from_utf8(&self.ctx().buffer),
            str::from_utf8(&self.ctx().buffer2),
            str::from_utf8(&self.bin_label),
        );

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(arena: &mut Arena, s: &str) -> Result<Vec<TermToken>> {
        let mut lx = TermLexer::try_new(s.bytes().fuse(), Some(OperDefs::new()))?;
        Ok(lx.try_collect(arena)?)
    }

    #[test]
    fn test_atoms() {
        let mut arena = Arena::new();
        let ts = lex(&mut arena, "\na+foo-x '^&%^&%^&%''abc' 'AAA'").unwrap();
        dbg!(&ts);
        assert!(ts.len() == 9);
        assert!(ts.iter().take(ts.len() - 1).all(|t| {
            t.line_no == 2
                && matches!(
                    Term::try_from(t.value.clone())
                        .unwrap()
                        .view(&arena)
                        .unwrap(),
                    View::Atom(_)
                )
        }));
    }

    #[test]
    fn test_bin() {
        let mut arena = Arena::new();
        let ts = lex(&mut arena, "% single line comment\nbin{3:\x00\x01\x02 eob:\x00\x01:aaa\x02:eob eob\n\x00\neob eob\r\n\x00\r\neob\r\n}\r\nhex{   0203 0405 FE }").unwrap();
        dbg!(&ts);
        assert!(ts.len() == 3);
        assert!(matches!(
            Term::try_from(ts[0].value.clone())
                .unwrap()
                .view(&arena)
                .unwrap(),
            View::Bin(_)
        ));
        match Term::try_from(ts[0].value.clone())
            .unwrap()
            .view(&arena)
            .unwrap()
        {
            View::Bin(bytes) => assert!(bytes == &[0, 1, 2, 0, 1, 58, 97, 97, 97, 2, 0, 0,]),
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_text() {
        let mut arena = Arena::new();
        let ts = lex(&mut arena, "/* single /* line */ comment */\ntext{3:abc eob:de:aaa:eob eob\n0\neob eob\r\n1\r\neob\r\n}\r\n").unwrap();
        dbg!(&ts);
        assert!(ts.len() == 2);
        assert!(matches!(
            Term::try_from(ts[0].value.clone())
                .unwrap()
                .view(&arena)
                .unwrap(),
            View::Str(_)
        ));
        match Term::try_from(ts[0].value.clone())
            .unwrap()
            .view(&arena)
            .unwrap()
        {
            View::Str(s) => assert!(s == "abcde:aaa01"),
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_texts() {
        let mut arena = Arena::new();
        let ts = lex(&mut arena, "/* single [ ( { /* line */ comment */\n\"hello\" {hello} text{5:hello} text{e:hello:e} text{e:h:e e:e:e 2:ll e:o:e} text{\ne\nhello\ne}").unwrap();
        dbg!(&ts);
        assert!(ts.len() == 7);
        assert!(matches!(
            Term::try_from(ts[0].value.clone())
                .unwrap()
                .view(&arena)
                .unwrap(),
            View::Str(_)
        ));
        assert!(ts.iter().take(ts.len() - 1).all(|t| {
            match Term::try_from(t.value.clone())
                .unwrap()
                .view(&arena)
                .unwrap()
            {
                View::Str(s) => s == "hello",
                _ => false,
            }
        }));
    }

    #[test]
    fn test_integers() {
        let mut arena = Arena::new();
        let ts = lex(&mut arena, "[2'01010001111, 10'123, 36'AZ]").unwrap();
        dbg!(&ts);
        assert!(ts.len() == 8);
        assert!(matches!(ts[1].token_id, TokenID::Int));
    }
}
