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

pub trait ParserStateID: Clone + Copy + Debug + PartialEq + Eq + Into<usize> {
    const COUNT: usize;
}

pub trait ParserAmbigID: Clone + Copy + Debug + PartialEq + Eq + Into<usize> {
    const COUNT: usize;
}

pub trait ParserProdID: Clone + Copy + Debug + PartialEq + Eq + Into<usize> {
    const COUNT: usize;
}

pub trait ParserTokenID: Clone + Copy + Debug + PartialEq + Eq + Into<usize> {
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

    fn start_state(&self) -> Self::StateID;

    fn lookup(
        &self,
        state_id: Self::StateID,
        token_id: Self::TokenID,
    ) -> ParserAction<Self::StateID, Self::ProdID, Self::AmbigID>;

    fn lookup_ambig(
        &self,
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
        let mut state = self.ctx().data.start_state();
        self.ctx_mut().states.push(state);
        if log::log_enabled!(log::Level::Trace) {
            self.ctx().dump_state(&token);
        }
        loop {
            let action = match self.ctx().data.lookup(state, token.token_id()) {
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
                    let Action::<Self>::Goto(new_state) = self.ctx().data.lookup(state, lhs_id)
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
    pub data: D,
    pub tokens: Vec<L::Token>,
    pub states: Vec<D::StateID>,
    pub stats: ParserStats,
}

impl<L, D> ParserCtx<L, D>
where
    L: Lexer,
    D: ParserData,
{
    pub fn new(lexer: L, data: D) -> Self {
        Self {
            data,
            lexer,
            tokens: Vec::new(),
            states: Vec::new(),
            stats: ParserStats::default(),
        }
    }

    /// Returns a reference to the token counted from the end:
    /// 0 = last, 1 = second last, etc.  
    /// Panics if `index` ≥ number of tokens.
    fn tokens_peek(&self, index: usize) -> &L::Token {
        let n = self.tokens.len();
        &self.tokens[n - 1 - index]
    }

    /// Returns a mutable reference to the token counted from the end:
    /// 0 = last, 1 = second last, etc.  
    /// Panics if `index` ≥ number of tokens.
    fn tokens_mut_peek(&mut self, index: usize) -> &mut L::Token {
        let n = self.tokens.len();
        &mut self.tokens[n - 1 - index]
    }

    fn tokens_pop(&mut self) -> Result<L::Token> {
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
