#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Mode {
    Expr = 0,
}

impl LexerMode for Mode {
    const COUNT: usize = 1;
}

impl From<Mode> for usize {
    fn from(m: Mode) -> Self {
        m as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Rule {
    Empty = 0,
    A = 1, // <Expr> .
    End = 2,
}

impl LexerRule for Rule {
    const COUNT: usize = 3;
    const END: Self = Self::End;
}

impl From<Rule> for usize {
    fn from(r: Rule) -> Self {
        r as usize
    }
}

pub struct LexData;
impl LexData {
    const START_MODE: Mode = Mode::Expr;

    const TAB: &'static [[Rule; 1]] = &[
        /* MODE 0 "Expr" */ [
            Rule::A,
        ],
    ];

    #[cfg(target_endian = "little")]
    const DFA_BYTES: &'static [u8] = &[];
    #[cfg(target_endian = "big")]
    const DFA_BYTES: &'static [u8] = &[];

    const DFA_OFFSETS: &'static [usize] = &[
        0, // Expr
    ];
}

impl LexerData for LexData {
    type LexerMode = Mode;
    type LexerRule = Rule;

    #[inline]
    fn start_mode() -> Self::LexerMode {
        Self::START_MODE
    }
    #[inline]
    fn dfa_bytes() -> &'static [u8] {
        Self::DFA_BYTES
    }
    #[inline]
    fn dfa_offsets() -> &'static [usize] {
        Self::DFA_OFFSETS
    }
    #[inline]
    fn lookup(mode: Self::LexerMode, pattern_id: usize) -> Self::LexerRule {
        Self::TAB[Into::<usize>::into(mode)][pattern_id]
    }
}

