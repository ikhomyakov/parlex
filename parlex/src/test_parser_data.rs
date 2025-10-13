#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StateID(u8);
impl ParserStateID for StateID {
    const COUNT: usize = 2;
}

impl From<StateID> for usize {
    fn from(s: StateID) -> Self {
        s.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AmbigID(u8);
impl ParserAmbigID for AmbigID {
    const COUNT: usize = 0;
}

impl From<AmbigID> for usize {
    fn from(a: AmbigID) -> Self {
        a.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ProdID {
   Start = 0,
   Rule1 = 1,
}

impl ParserProdID for ProdID {
    type TokenID = TokenID;

    const COUNT: usize = 2;

    fn label(&self) -> &'static str {
        ProdID::LABELS[Into::<usize>::into(*self)]
    }
    fn lhs_token_id(&self) -> Self::TokenID {
        ProdID::LHS_TOKENS[Into::<usize>::into(*self)]
    }
    fn size(&self) -> usize {
        ProdID::SIZES[Into::<usize>::into(*self)]
    }
}

impl From<ProdID> for usize {
    fn from(p: ProdID) -> Self {
        p as usize
    }
}

impl ProdID {
    pub const LABELS: &'static [&str] = &[
       "start", // 0
       "rule1", // 1
    ];

    pub const LHS_TOKENS: &[TokenID] = &[
        TokenID::Start, // 0
        TokenID::S, // 1
    ];

    pub const SIZES: &[usize] = &[
        1, // 0
        0, // 1
    ];

}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TokenID {
    // Nonterminals:
    Start = 0,
    S = 1,

        // Terminals:
    End = 2,

        // Error:
    Error = 3,
}

impl ParserTokenID for TokenID {
    const COUNT_NONTERMINALS: usize = 2;
    const COUNT_TERMINALS: usize = 1;
    const COUNT: usize = Self::COUNT_NONTERMINALS + Self::COUNT_TERMINALS + 1;

    fn label(&self) -> &'static str {
        TokenID::LABELS[Into::<usize>::into(*self)]
    }
}

impl From<TokenID> for usize {
    fn from(t: TokenID) -> Self {
        t as usize
    }
}

impl TokenID {
    pub const LABELS: &'static [&str] = &[
        "Start", // 0
        "S", // 1
        "end", // 2
        "error", // 3
    ];

}

pub type Action = ParserAction<StateID, ProdID, AmbigID>;

pub struct ParData;
impl ParData {
    const TAB: &'static [[Action; TokenID::COUNT - 1]] = &[
        /* STATE 0 */ [
            Action::Error, /* 0(Start) */
            Action::Goto(StateID(1)), /* 1(S) */
            Action::Reduce(ProdID::Rule1), /* 2(end) */
        ],
        /* STATE 1 */ [
            Action::Error, /* 0(Start) */
            Action::Error, /* 1(S) */
            Action::Accept, /* 2(end) */
        ],
    ];

    const AMBIGS: &'static [[Action; 2]] = &[
    ];

}

impl ParserData for ParData {
    type StateID = StateID;
    type AmbigID = AmbigID;
    type TokenID = TokenID;
    type ProdID = ProdID;

    #[inline]
    fn start_state() -> Self::StateID {
        StateID(0)
    }
    #[inline]
    fn lookup(state_id: StateID, token_id: TokenID) -> Action {
        Self::TAB[Into::<usize>::into(state_id)][Into::<usize>::into(token_id)]
    }
    #[inline]
    fn lookup_ambig(ambig_id: AmbigID) -> &'static [Action; 2] {
        &Self::AMBIGS[Into::<usize>::into(ambig_id)]
    }
}

