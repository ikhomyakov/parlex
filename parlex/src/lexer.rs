use anyhow::{Result, anyhow, bail};
use regex_automata::{
    Anchored, HalfMatch, Input,
    dfa::{Automaton, dense},
    util::primitives::PatternID,
};
use smartstring::alias::String;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::iter::FusedIterator;
use std::mem;

pub trait Token: Copy + Debug {
    type TokenID: Into<usize>;

    fn token_id(&self) -> Self::TokenID;
    fn line_no(&self) -> usize;
}

pub trait LexerMode: Copy + Debug + Into<usize> {
    const COUNT: usize;
}

pub trait LexerRule: Copy + Debug + Into<usize> {
    const COUNT: usize;
    const END: Self;
}

pub trait LexerData {
    type LexerMode: LexerMode;
    type LexerRule: LexerRule;

    fn start_mode(&self) -> Self::LexerMode;
    fn dfa_bytes(&self) -> &'static [u8];

    fn lookup(&self, mode: Self::LexerMode, pattern_id: PatternID) -> Self::LexerRule;
}

pub trait Lexer {
    type Input: FusedIterator<Item = u8>;
    type LexerData: LexerData;
    type Token: Token;

    fn ctx(&self) -> &LexerCtx<Self::Input, Self::LexerData, Self::Token>;
    fn ctx_mut(&mut self) -> &mut LexerCtx<Self::Input, Self::LexerData, Self::Token>;

    fn action(&mut self, rule: <Self::LexerData as LexerData>::LexerRule) -> Result<()>;

    fn stats(&self) -> LexerStats {
        self.ctx().stats.clone()
    }

    #[inline]
    fn try_next(&mut self) -> Result<Option<Self::Token>> {
        if let Some(t) = self.ctx_mut().tokens.pop_front() {
            return Ok(Some(t));
        }

        if self.ctx().end_flag {
            return Ok(None);
        }

        while let Some(pattern) = self.ctx_mut().try_match()? {
            let mode = self.ctx().mode;
            let rule = self.ctx().data.lookup(mode, pattern);
            log::trace!(
                "MATCHED: LexerMode: {:?}, LexerRule: {:?}, Pattern: {}, Buffer: {:?}, Buffer2: {:?}",
                mode,
                rule,
                pattern.as_usize(),
                match str::from_utf8(&self.ctx().buffer) {
                    Ok(s) => s,
                    Err(_) => &hex::encode(&self.ctx().buffer),
                },
                match str::from_utf8(&self.ctx().buffer2) {
                    Ok(s) => s,
                    Err(_) => &hex::encode(&self.ctx().buffer2),
                },
            );

            self.action(rule)?;

            if let Some(t) = self.ctx_mut().tokens.pop_front() {
                return Ok(Some(t));
            }
        }
        self.ctx_mut().end_flag = true;

        self.action(<Self::LexerData as LexerData>::LexerRule::END)?;

        if let Some(t) = self.ctx_mut().tokens.pop_front() {
            return Ok(Some(t));
        } else {
            return Ok(None);
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct LexerStats {
    pub unreads: usize,
    pub chars: usize,
    pub matches: usize,
}

pub struct LexerCtx<I, D, T>
where
    D: LexerData,
{
    pub mode: D::LexerMode,

    data: D,
    dfas: Vec<dense::DFA<&'static [u32]>>,

    input: I,
    unread: Vec<u8>,

    accum_flag: bool,
    pub buffer: Vec<u8>,
    pub buffer2: Vec<u8>,

    end_flag: bool,
    tokens: VecDeque<T>,

    pub line_no: usize,

    stats: LexerStats,
}

impl<I, D, T> LexerCtx<I, D, T>
where
    I: FusedIterator<Item = u8>,
    D: LexerData,
    T: Token,
{
    pub fn try_new(input: I, data: D) -> Result<Self> {
        let mut dfas = Vec::new();
        let dfa_bytes = data.dfa_bytes();
        let mut offset = 0;
        for _ in 0..D::LexerMode::COUNT {
            let (dfa, len) = dense::DFA::from_bytes(&dfa_bytes[offset..])?;
            dfas.push(dfa);
            offset += len;
        }

        Ok(Self {
            mode: data.start_mode(),
            data,
            dfas,
            input,
            unread: Vec::new(),
            accum_flag: false,
            buffer: Vec::new(),
            buffer2: Vec::new(),
            end_flag: false,
            tokens: VecDeque::new(),
            line_no: 1,
            stats: LexerStats::default(),
        })
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

    fn begin(&mut self, mode: D::LexerMode) {
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
        struct XLexerMode;
        impl LexerMode for XLexerMode {
            const COUNT: usize = 0;
        }
        impl Into<usize> for XLexerMode {
            fn into(self) -> usize {
                0
            }
        }

        #[derive(Debug, Clone, Copy)]
        struct XLexerRule;
        impl LexerRule for XLexerRule {
            const COUNT: usize = 0;
            const END: Self = Self;
        }
        impl Into<usize> for XLexerRule {
            fn into(self) -> usize {
                0
            }
        }

        #[derive(Debug, Clone, Copy)]
        struct XToken {
            token_id: usize,
            line_no: usize,
        }
        impl Token for XToken {
            type TokenID = usize;

            fn token_id(&self) -> Self::TokenID {
                self.token_id
            }
            fn line_no(&self) -> usize {
                self.line_no
            }
        }

        struct XLexerData {}
        impl LexerData for XLexerData {
            type LexerMode = XLexerMode;
            type LexerRule = XLexerRule;

            fn start_mode(&self) -> Self::LexerMode {
                XLexerMode
            }
            fn dfa_bytes(&self) -> &'static [u8] {
                &[]
            }

            #[inline]
            fn lookup(&self, _mode: Self::LexerMode, _pattern_id: PatternID) -> Self::LexerRule {
                XLexerRule
            }
        }

        struct XLexer<I>
        where
            I: FusedIterator<Item = u8>,
        {
            ctx: LexerCtx<I, <Self as Lexer>::LexerData, <Self as Lexer>::Token>,
        }

        impl<I> XLexer<I>
        where
            I: FusedIterator<Item = u8>,
        {
            fn try_new(input: I, data: XLexerData) -> Result<Self> {
                let mut ctx = LexerCtx::try_new(input, data)?;
                ctx.end_flag = true;
                Ok(Self { ctx })
            }
        }

        impl<I> Lexer for XLexer<I>
        where
            I: FusedIterator<Item = u8>,
        {
            type Input = I;
            type LexerData = XLexerData;
            type Token = XToken;

            fn ctx(&self) -> &LexerCtx<Self::Input, Self::LexerData, Self::Token> {
                &self.ctx
            }
            fn ctx_mut(&mut self) -> &mut LexerCtx<Self::Input, Self::LexerData, Self::Token> {
                &mut self.ctx
            }

            fn action(&mut self, _rule: <Self::LexerData as LexerData>::LexerRule) -> Result<()> {
                self.ctx_mut().yield_token(XToken {
                    token_id: 0,
                    line_no: 0,
                });
                Ok(())
            }
        }

        let s = "hello";
        let mut lexer = XLexer::try_new(s.bytes().fuse(), XLexerData {}).unwrap();
        while let Some(t) = lexer.try_next().unwrap() {
            dbg!(t);
        }
    }
}
