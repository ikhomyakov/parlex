use anyhow::{Result, anyhow, bail};
use regex_automata::{
    Anchored, HalfMatch, Input,
    dfa::{Automaton, dense},
    util::primitives::PatternID,
};
use smartstring::alias::String;
use std::collections::VecDeque;
use std::iter::FusedIterator;
use std::mem;

pub trait Mode: Sized + Copy + std::fmt::Debug + Into<usize> {
    const COUNT: usize;
}

pub trait Rule: Sized + Copy + std::fmt::Debug + Into<usize> {
    const COUNT: usize;
    const END: Self;
}

pub trait Token: Sized + Copy + std::fmt::Debug {}

pub trait LexerTab {
    type Mode: Mode;
    type Rule: Rule;

    fn lookup(&self, mode: Self::Mode, pattern_id: PatternID) -> Self::Rule;
}

pub trait Lexer<I>
where
    I: FusedIterator<Item = u8>,
{
    type LexerTab: LexerTab;
    type Token: Token;

    fn base(&self) -> &LexerBase<I, Self::LexerTab, Self::Token>;
    fn base_mut(&mut self) -> &mut LexerBase<I, Self::LexerTab, Self::Token>;

    fn action(&mut self, rule: <<Self as Lexer<I>>::LexerTab as LexerTab>::Rule);

    fn try_next(&mut self) -> Result<Option<Self::Token>> {
        if let Some(t) = self.base_mut().tokens.pop_front() {
            return Ok(Some(t));
        }

        if self.base().end_flag {
            return Ok(None);
        }

        while let Some(pattern) = self.base_mut().try_match()? {
            let mode = self.base().mode;
            let rule = self.base_mut().tab.lookup(mode, pattern);
            log::trace!(
                "MATCHED: Mode: {:?}, Rule: {:?}, Pattern: {}, Buffer: {:?}, Buffer2: {:?}",
                self.base().mode,
                rule,
                pattern.as_usize(),
                match str::from_utf8(&self.base().buffer) {
                    Ok(s) => s,
                    Err(_) => &hex::encode(&self.base().buffer),
                },
                match str::from_utf8(&self.base().buffer2) {
                    Ok(s) => s,
                    Err(_) => &hex::encode(&self.base().buffer2),
                },
            );

            self.action(rule);

            if let Some(t) = self.base_mut().tokens.pop_front() {
                return Ok(Some(t));
            }
        }
        self.base_mut().end_flag = true;

        self.action(<<Self as Lexer<I>>::LexerTab as LexerTab>::Rule::END);

        if let Some(t) = self.base_mut().tokens.pop_front() {
            return Ok(Some(t));
        } else {
            return Ok(None);
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Stats {
    pub unreads: usize,
    pub chars: usize,
    pub matches: usize,
}

pub struct LexerBase<I, L, T>
where
    I: FusedIterator<Item = u8>,
    L: LexerTab,
    T: Token,
{
    pub mode: L::Mode,

    tab: L,
    dfas: Vec<dense::DFA<&'static [u32]>>,

    input: I,
    unread: Vec<u8>,

    accum_flag: bool,
    pub buffer: Vec<u8>,
    pub buffer2: Vec<u8>,

    end_flag: bool,
    tokens: VecDeque<T>,

    pub line_no: usize,

    stats: Stats,
}

impl<I, L, T> LexerBase<I, L, T>
where
    I: FusedIterator<Item = u8>,
    L: LexerTab,
    T: Token,
{
    pub fn try_new(input: I, tab: L, dfa_bytes: &'static [u8], start: L::Mode) -> Result<Self> {
        let mut dfas = Vec::new();
        let mut offset = 0;
        for _ in 0..L::Mode::COUNT {
            let (dfa, len) = dense::DFA::from_bytes(&dfa_bytes[offset..])?;
            dfas.push(dfa);
            offset += len;
        }

        Ok(Self {
            mode: start,
            tab,
            dfas,
            input,
            unread: Vec::new(),
            accum_flag: false,
            buffer: Vec::new(),
            buffer2: Vec::new(),
            end_flag: false,
            tokens: VecDeque::new(),
            line_no: 1,
            stats: Stats::default(),
        })
    }

    pub fn stats(&self) -> Stats {
        self.stats
    }

    fn try_match(&mut self) -> Result<Option<PatternID>> {
        self.stats.matches += 1;
        if !self.accum_flag {
            self.buffer.clear();
        }
        let dfa = &self.dfas[self.mode.into()];
        let mut state = dfa.start_state_forward(&Input::new(&[]).anchored(Anchored::Yes))?;
        log::trace!(
            "START: mode={}, s={}",
            Into::<usize>::into(self.mode),
            state.as_usize()
        );
        let mut last_match = None;
        let mut i = 0;

        loop {
            match self.unread.pop().or_else(|| {
                self.stats.chars += 1;
                self.input.next()
            }) {
                Some(b) => {
                    self.buffer.push(b);
                    state = dfa.next_state(state, b);
                    if dfa.is_special_state(state) {
                        if dfa.is_match_state(state) {
                            log::trace!(
                                "MATCH: i={}, b={:?}, n={}, p={}, s={}",
                                i,
                                b as char,
                                dfa.match_len(state),
                                dfa.match_pattern(state, 0).as_usize(),
                                state.as_usize()
                            );
                            last_match = Some(HalfMatch::new(dfa.match_pattern(state, 0), i));
                        } else if dfa.is_dead_state(state) || dfa.is_quit_state(state) {
                            if dfa.is_dead_state(state) {
                                log::trace!(
                                    "DEAD: i={}, b={:?}, s={}",
                                    i,
                                    b as char,
                                    state.as_usize()
                                );
                            } else {
                                log::trace!(
                                    "QUIT: i={}, b={:?}, s={}",
                                    i,
                                    b as char,
                                    state.as_usize()
                                );
                            }
                            match last_match {
                                Some(m) => {
                                    for _ in 0..i - m.offset() + 1 {
                                        match self.buffer.pop() {
                                            Some(x) => self.unread.push(x),
                                            None => bail!("Overpop!"),
                                        }
                                    }
                                    return Ok(Some(m.pattern()));
                                }
                                None => {
                                    bail!("Bad byte {:?}", b);
                                }
                            }
                        }
                    } else {
                        log::trace!(
                            "OTHER: i={}, b={:?}, s={}; match={}, dead={}, quit={}, start={}, accel={}",
                            i,
                            b as char,
                            state.as_usize(),
                            dfa.is_match_state(state),
                            dfa.is_dead_state(state),
                            dfa.is_quit_state(state),
                            dfa.is_start_state(state),
                            dfa.is_accel_state(state),
                        );
                    }
                }
                None => break,
            }
            i = i + 1;
        }
        state = dfa.next_eoi_state(state);
        if dfa.is_match_state(state) {
            last_match = Some(HalfMatch::new(dfa.match_pattern(state, 0), i));
        }
        match last_match {
            Some(m) => {
                for _ in 0..i - m.offset() {
                    self.stats.unreads += 1;
                    match self.buffer.pop() {
                        Some(x) => self.unread.push(x),
                        None => bail!("Overpop!"),
                    }
                }
                return Ok(Some(m.pattern()));
            }
            None => {
                return Ok(None);
            }
        }
    }

    fn accum(&mut self) {
        self.accum_flag = true;
    }

    fn begin(&mut self, mode: L::Mode) {
        self.mode = mode;
    }

    fn yield_token(&mut self, token: T) {
        self.tokens.push_back(token);
    }

    fn clear(&mut self) {
        self.accum_flag = false;
        self.buffer.clear();
    }

    fn take_bytes(&mut self) -> Vec<u8> {
        self.accum_flag = false;
        mem::take(&mut self.buffer)
    }

    fn take_bytes2(&mut self) -> Vec<u8> {
        self.accum_flag = false;
        self.buffer.clear();
        mem::take(&mut self.buffer2)
    }

    fn take_str(&mut self) -> Result<String> {
        let bytes = self.take_bytes();
        let s = std::string::String::from_utf8(bytes)?;
        Ok(s.into())
    }

    fn take_str2(&mut self) -> Result<String> {
        let bytes = self.take_bytes2();
        let s = std::string::String::from_utf8(bytes)?;
        Ok(s.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_lexer() {
        #[derive(Debug, Clone, Copy)]
        struct XMode;
        impl Mode for XMode {
            const COUNT: usize = 0;
        }
        impl Into<usize> for XMode {
            fn into(self) -> usize {
                0
            }
        }

        #[derive(Debug, Clone, Copy)]
        struct XRule;
        impl Rule for XRule {
            const COUNT: usize = 0;
            const END: Self = Self;
        }
        impl Into<usize> for XRule {
            fn into(self) -> usize {
                0
            }
        }

        #[derive(Debug, Clone, Copy)]
        struct XToken;
        impl Token for XToken {}

        struct XLexerTab {}
        impl LexerTab for XLexerTab {
            type Mode = XMode;
            type Rule = XRule;

            fn lookup(&self, mode: Self::Mode, pattern_id: PatternID) -> Self::Rule {
                XRule
            }
        }

        struct XLexer<I>
        where
            I: FusedIterator<Item = u8>,
        {
            base: LexerBase<I, <Self as Lexer<I>>::LexerTab, <Self as Lexer<I>>::Token>,
        }
        impl<I> XLexer<I>
        where
            I: FusedIterator<Item = u8>,
        {
            fn try_new(
                input: I,
                tab: XLexerTab,
                dfa_bytes: &'static [u8],
                start: XMode,
            ) -> Result<Self> {
                let mut base = LexerBase::try_new(input, tab, dfa_bytes, start)?;
                base.end_flag = true;
                Ok(Self { base })
            }
        }
        impl<I> Lexer<I> for XLexer<I>
        where
            I: FusedIterator<Item = u8>,
        {
            type LexerTab = XLexerTab;
            type Token = XToken;

            fn base(&self) -> &LexerBase<I, Self::LexerTab, Self::Token> {
                &self.base
            }
            fn base_mut(&mut self) -> &mut LexerBase<I, Self::LexerTab, Self::Token> {
                &mut self.base
            }

            fn action(&mut self, _rule: <<Self as Lexer<I>>::LexerTab as LexerTab>::Rule) {
                self.base_mut().yield_token(XToken {});
            }
        }

        let s = "hello";
        let mut lexer = XLexer::try_new(s.bytes().fuse(), XLexerTab {}, &[], XMode {}).unwrap();
        while let Some(t) = lexer.try_next().unwrap() {
            dbg!(t);
        }
    }
}
