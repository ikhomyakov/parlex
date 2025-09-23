use crate::{Lexer, Token};
use anyhow::{Result, anyhow, bail};
use smartstring::alias::String;
use std::fmt::Debug;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParserAction<US, UP, UA>
where
    US: ParserStateID,
    UP: ParserProdID,
    UA: ParserAmbigID,
{
    Error,
    Accept,
    Shift(US),
    Reduce(UP),
    Ambig(UA),
    Goto(US),
}

pub trait ParserStateID: Copy + Debug + Eq + Into<usize> {
    const COUNT: usize;
}

pub trait ParserAmbigID: Copy + Debug + Eq + Into<usize> {
    const COUNT: usize;
}

pub trait ParserProdID: Copy + Debug + Eq + Into<usize> {
    const COUNT: usize;
}

pub trait ParserTokenID: Copy + Debug + Eq + Into<usize> {
    const COUNT_NONTERMINALS: usize;
    const COUNT_TERMINALS: usize;
    const COUNT: usize;
}

type Action<P> = ParserAction<
    <<P as Parser>::ParserData as ParserData>::StateID,
    <<P as Parser>::ParserData as ParserData>::ProdID,
    <<P as Parser>::ParserData as ParserData>::AmbigID,
>;

pub trait ParserData {
    type StateID: ParserStateID;
    type AmbigID: ParserAmbigID;
    type TokenID: ParserTokenID;
    type ProdID: ParserProdID;

    fn start_state() -> Self::StateID;

    fn lookup(
        state_id: Self::StateID,
        token_id: Self::TokenID,
    ) -> ParserAction<Self::StateID, Self::ProdID, Self::AmbigID>;

    fn lookup_ambig(
        ambig_id: Self::AmbigID,
    ) -> [ParserAction<Self::StateID, Self::ProdID, Self::AmbigID>; 2];
}

pub trait Parser {
    type Lexer: Lexer<Token: Token<TokenID = <Self::ParserData as ParserData>::TokenID>>;
    type ParserData: ParserData;

    fn ctx(&self) -> &ParserCtx<Self::Lexer, Self::ParserData>;
    fn ctx_mut(&mut self) -> &mut ParserCtx<Self::Lexer, Self::ParserData>;

    fn resolve_ambiguity(
        &mut self,
        ambig: <Self::ParserData as ParserData>::AmbigID,
        tok2: &<Self::Lexer as Lexer>::Token,
    ) -> Result<Action<Self>>;

    fn reduce(
        &mut self,
        prod_id: <Self::ParserData as ParserData>::ProdID,
        token: &<Self::Lexer as Lexer>::Token,
    ) -> Result<()>;

    fn stats(&self) -> ParserStats {
        self.ctx().stats.clone()
    }

    #[inline]
    fn try_next(&mut self) -> Result<Option<<Self::Lexer as Lexer>::Token>> {
        self.ctx_mut().states.clear();
        self.ctx_mut().tokens.clear();
        self.ctx_mut().stats.tokens += 1;
        let mut token = match self.ctx_mut().lexer.try_next()? {
            Some(t) => t,
            None => {
                return Ok(None);
            }
        };
        let mut state = <Self as Parser>::ParserData::start_state();
        self.ctx_mut().states.push(state);
        if log::log_enabled!(log::Level::Trace) {
            self.ctx().dump_state(&token);
        }
        loop {
            let action = match <Self as Parser>::ParserData::lookup(state, token.token_id()) {
                Action::<Self>::Ambig(ambig) => {
                    log::trace!("Ambig {:?}", ambig);
                    let action = self.resolve_ambiguity(ambig, &mut token)?;
                    self.ctx_mut().stats.ambigs += 1;
                    action
                }
                action => action,
            };
            match action {
                Action::<Self>::Shift(new_state) => {
                    log::trace!("Shift {:?}", new_state);
                    self.ctx_mut().tokens.push(token);
                    state = new_state;
                    self.ctx_mut().states.push(state);
                    self.ctx_mut().stats.tokens += 1;
                    token = match self.ctx_mut().lexer.try_next()? {
                        Some(t) => t,
                        None => bail!("unexpected end of stream"),
                    };
                    self.ctx_mut().stats.shifts += 1;
                }

                Action::<Self>::Reduce(prod_id) => {
                    let prod_id_idx: usize = prod_id.into();
                    log::trace!("Reduce {:?}({})", prod_id, prod_id_idx);
                    self.reduce(prod_id, &token)?;
                    state = self.ctx().states[self.ctx().states.len() - 1];
                    let lhs_id = self.ctx().tokens[self.ctx().tokens.len() - 1].token_id();
                    let Action::<Self>::Goto(new_state) =
                        <Self as Parser>::ParserData::lookup(state, lhs_id)
                    else {
                        bail!("expected Action::Goto");
                    };
                    state = new_state;
                    self.ctx_mut().states.push(state);
                    self.ctx_mut().stats.reductions += 1;
                }

                Action::<Self>::Accept => {
                    log::trace!("Accept");
                    assert!(self.ctx().tokens.len() == 1);
                    let token = self.ctx_mut().tokens_pop()?;
                    return Ok(Some(token));
                }

                Action::<Self>::Error => {
                    bail!("Error on token {:?}", token)
                }

                Action::<Self>::Ambig(_) | Action::<Self>::Goto(_) => unreachable!(),
            }

            if log::log_enabled!(log::Level::Trace) {
                self.ctx().dump_state(&token);
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct ParserStats {
    pub tokens: usize,
    pub shifts: usize,
    pub reductions: usize,
    pub ambigs: usize,
}

pub struct ParserCtx<L, D>
where
    L: Lexer,
    D: ParserData,
{
    pub lexer: L,
    pub tokens: Vec<L::Token>,
    pub states: Vec<D::StateID>,
    pub stats: ParserStats,
}

impl<L, D> ParserCtx<L, D>
where
    L: Lexer,
    D: ParserData,
{
    pub fn new(lexer: L) -> Self {
        Self {
            lexer,
            tokens: Vec::new(),
            states: Vec::new(),
            stats: ParserStats::default(),
        }
    }

    /// Returns a reference to the token counted from the end:
    /// 0 = last, 1 = second last, etc.  
    /// Panics if `index` ≥ number of tokens.
    pub fn tokens_peek(&self, index: usize) -> &L::Token {
        let n = self.tokens.len();
        &self.tokens[n - 1 - index]
    }

    /// Returns a mutable reference to the token counted from the end:
    /// 0 = last, 1 = second last, etc.  
    /// Panics if `index` ≥ number of tokens.
    pub fn tokens_mut_peek(&mut self, index: usize) -> &mut L::Token {
        let n = self.tokens.len();
        &mut self.tokens[n - 1 - index]
    }

    pub fn tokens_pop(&mut self) -> Result<L::Token> {
        self.tokens.pop().ok_or_else(|| anyhow!("stack underflow"))
    }

    pub fn dump_state(&self, incoming: &L::Token) {
        let mut output = String::new();
        if !self.states.is_empty() {
            for (i, (token, state)) in self
                .tokens
                .iter()
                .chain(std::iter::once(incoming))
                .zip(self.states.iter())
                .enumerate()
            {
                output.push_str(&format!(
                    "<{:?}>  {}{:?}  ",
                    state,
                    if i == self.states.len() - 1 {
                        "<-  "
                    } else {
                        ""
                    },
                    token,
                ));
            }
            log::trace!("{}", output);
        } else {
            log::trace!("<>");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Action;
    use crate::lexer::{Lexer, LexerCtx, LexerData, LexerMode, LexerRule, LexerStats, Token};
    use crate::parser::{
        Parser, ParserAction, ParserAmbigID, ParserCtx, ParserData, ParserProdID, ParserStateID,
        ParserStats, ParserTokenID,
    };
    use anyhow::{Result, anyhow, bail};
    use regex_automata::PatternID;
    use smartstring::alias::String;
    use std::fmt::Debug;
    use std::iter::FusedIterator;

    fn init_logger() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

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

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct TokenID(usize);

    impl From<TokenID> for usize {
        fn from(token_id: TokenID) -> Self {
            token_id.0
        }
    }

    impl ParserTokenID for TokenID {
        const COUNT_NONTERMINALS: usize = 5;
        const COUNT_TERMINALS: usize = 10;
        const COUNT: usize = 15;
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
    struct StateID(usize);

    impl From<StateID> for usize {
        fn from(state_id: StateID) -> Self {
            state_id.0
        }
    }

    impl ParserStateID for StateID {
        const COUNT: usize = 45;
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct ProdID(usize);

    impl From<ProdID> for usize {
        fn from(prod_id: ProdID) -> Self {
            prod_id.0
        }
    }

    impl ParserProdID for ProdID {
        const COUNT: usize = 24;
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct AmbigID(usize);

    impl From<AmbigID> for usize {
        fn from(token_id: AmbigID) -> Self {
            token_id.0
        }
    }

    impl ParserAmbigID for AmbigID {
        const COUNT: usize = 1500;
    }

    #[derive(Debug, Clone, Copy)]
    struct XToken {
        token_id: TokenID,
        line_no: usize,
    }
    impl Token for XToken {
        type TokenID = TokenID;

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

        fn start_mode() -> Self::LexerMode {
            XLexerMode
        }
        fn dfa_bytes() -> &'static [u8] {
            &[]
        }

        #[inline]
        fn lookup(_mode: Self::LexerMode, _pattern_id: usize) -> Self::LexerRule {
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
        fn try_new(input: I) -> Result<Self> {
            let mut ctx = LexerCtx::try_new(input)?;
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
                token_id: TokenID(0),
                line_no: 0,
            });
            Ok(())
        }
    }

    struct XParserData {}
    impl ParserData for XParserData {
        type StateID = StateID;
        type AmbigID = AmbigID;
        type TokenID = TokenID;
        type ProdID = ProdID;

        fn start_state() -> Self::StateID {
            StateID::default()
        }

        fn lookup(
            state_id: Self::StateID,
            token_id: Self::TokenID,
        ) -> ParserAction<Self::StateID, Self::ProdID, Self::AmbigID> {
            ParserAction::Accept
        }

        fn lookup_ambig(
            ambig_id: Self::AmbigID,
        ) -> [ParserAction<Self::StateID, Self::ProdID, Self::AmbigID>; 2] {
            [
                ParserAction::Shift(StateID::default()),
                ParserAction::Reduce(ProdID(0)),
            ]
        }
    }

    struct XParser<I>
    where
        I: FusedIterator<Item = u8>,
    {
        ctx: ParserCtx<XLexer<I>, <Self as Parser>::ParserData>,
    }

    impl<I> XParser<I>
    where
        I: FusedIterator<Item = u8>,
    {
        fn try_new(input: I) -> Result<Self> {
            let lexer = XLexer::try_new(input)?;
            let ctx = ParserCtx::new(lexer);
            Ok(Self { ctx })
        }
    }

    impl<I> Parser for XParser<I>
    where
        I: FusedIterator<Item = u8>,
    {
        type Lexer = XLexer<I>;
        type ParserData = XParserData;

        fn ctx(&self) -> &ParserCtx<Self::Lexer, Self::ParserData> {
            &self.ctx
        }
        fn ctx_mut(&mut self) -> &mut ParserCtx<Self::Lexer, Self::ParserData> {
            &mut self.ctx
        }

        fn resolve_ambiguity(
            &mut self,
            ambig: <Self::ParserData as ParserData>::AmbigID,
            tok2: &<Self::Lexer as Lexer>::Token,
        ) -> Result<Action<Self>> {
            Ok(Action::<Self>::Shift(StateID::default()))
        }

        fn reduce(
            &mut self,
            prod_id: <Self::ParserData as ParserData>::ProdID,
            token: &<Self::Lexer as Lexer>::Token,
        ) -> Result<()> {
            Ok(())
        }
    }

    #[test]
    fn empty_parser() {
        init_logger();
        let s = "hello";
        let mut parser = XParser::try_new(s.bytes().fuse()).unwrap();
        while let Some(t) = parser.try_next().unwrap() {
            dbg!(t);
        }
    }
}
