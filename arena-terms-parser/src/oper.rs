use anyhow::{Context, Result, anyhow, bail};
use arena_terms::{Arena, Term, View};
use indexmap::IndexMap;
use smartstring::alias::String;
use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Fixity {
    Fun = 0,
    Prefix = 1,
    Infix = 2,
    Postfix = 3,
}

impl Fixity {
    pub const COUNT: usize = 4;
    pub const STRS: &[&str] = &["fun", "prefix", "infix", "postfix"];
}

impl From<Fixity> for String {
    fn from(f: Fixity) -> Self {
        Fixity::STRS[Into::<usize>::into(f)].into()
    }
}

impl From<Fixity> for usize {
    fn from(f: Fixity) -> Self {
        f as usize
    }
}

impl fmt::Display for Fixity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(String::from(*self).as_str())
    }
}

#[derive(Debug, Clone)]
pub struct ParseFixityError(String);

impl fmt::Display for ParseFixityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid fixity: {}", self.0)
    }
}
impl std::error::Error for ParseFixityError {}

impl FromStr for Fixity {
    type Err = ParseFixityError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "fun" => Ok(Fixity::Fun),
            "prefix" => Ok(Fixity::Prefix),
            "infix" => Ok(Fixity::Infix),
            "postfix" => Ok(Fixity::Postfix),
            other => Err(ParseFixityError(String::from(other))),
        }
    }
}

impl TryFrom<&str> for Fixity {
    type Error = ParseFixityError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        s.parse()
    }
}

impl TryFrom<String> for Fixity {
    type Error = ParseFixityError;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        s.as_str().parse()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Assoc {
    None = 0,
    Left = 1,
    Right = 2,
}

impl Assoc {
    pub const COUNT: usize = 3;
    pub const STRS: &[&str] = &["none", "left", "right"];
}

impl From<Assoc> for String {
    fn from(a: Assoc) -> Self {
        Assoc::STRS[Into::<usize>::into(a)].into()
    }
}

impl From<Assoc> for usize {
    fn from(a: Assoc) -> Self {
        a as usize
    }
}

impl fmt::Display for Assoc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(String::from(*self).as_str())
    }
}

#[derive(Debug, Clone)]
pub struct ParseAssocError(String);

impl fmt::Display for ParseAssocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid associativity: {}", self.0)
    }
}
impl std::error::Error for ParseAssocError {}

impl FromStr for Assoc {
    type Err = ParseAssocError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "none" => Ok(Assoc::None),
            "left" => Ok(Assoc::Left),
            "right" => Ok(Assoc::Right),
            other => Err(ParseAssocError(String::from(other))),
        }
    }
}

impl TryFrom<&str> for Assoc {
    type Error = ParseAssocError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        s.parse()
    }
}

impl TryFrom<String> for Assoc {
    type Error = ParseAssocError;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        s.as_str().parse()
    }
}

#[derive(Debug, Clone)]
pub struct OperArg {
    pub name: String, // Atom
    pub default: Option<Term>,
}

pub const NON_OPER_PREC: usize = 0;
pub const MIN_OPER_PREC: usize = 0;
pub const MAX_OPER_PREC: usize = 1200;

#[derive(Debug, Clone)]
pub struct OperDef {
    pub fixity: Fixity,
    pub prec: usize,  // Precedence: 0 (Min) .. =1200 (Max), must be 0 for Fixity::Fun
    pub assoc: Assoc, // Must be Assoc::None for Fixity::Fun, Assoc::Right for Fixity::Prefix, and Assoc::Left for Fixity::Postfix.
    pub args: Vec<OperArg>, // Extra arguments beyond the operator’s required operands.
    pub rename_to: Option<Term>, // Atom
    pub embed_fixity: bool,
}

#[derive(Debug, Clone)]
pub struct OperDefTab {
    tab: [Option<OperDef>; Fixity::COUNT],
}

#[derive(Debug, Clone, Default)]
pub struct OperDefs {
    map: IndexMap<String, OperDefTab>,
}

static EMPTY_OPER_DEF_TAB: OperDefTab = OperDefTab::new();

impl OperDef {
    pub fn required_arity(fixity: Fixity) -> usize {
        match fixity {
            Fixity::Fun => 0,
            Fixity::Prefix => 1,
            Fixity::Infix => 2,
            Fixity::Postfix => 1,
        }
    }
}

impl OperDefTab {
    pub const fn new() -> Self {
        Self {
            tab: [const { None }; Fixity::COUNT],
        }
    }

    pub fn is_fun(&self) -> bool {
        self.tab[0].is_some()
    }

    pub fn is_oper(&self) -> bool {
        self.tab[1..].iter().any(|x| x.is_some())
    }

    pub fn get_op_def(&self, fixity: Fixity) -> Option<&OperDef> {
        self.tab[usize::from(fixity)].as_ref()
    }
}

impl std::ops::Index<Fixity> for OperDefTab {
    type Output = Option<OperDef>;
    fn index(&self, i: Fixity) -> &Self::Output {
        let i: usize = i.into();
        &self.tab[i]
    }
}

impl std::ops::IndexMut<Fixity> for OperDefTab {
    fn index_mut(&mut self, i: Fixity) -> &mut Self::Output {
        let i: usize = i.into();
        &mut self.tab[i]
    }
}

impl OperDefs {
    pub fn new() -> Self {
        Self {
            map: IndexMap::new(),
        }
    }

    pub fn try_from_ops(arena: &Arena, ops: Term) -> Result<Self> {
        let mut oper_defs = Self::new();
        oper_defs.define_opers(arena, ops)?;
        Ok(oper_defs)
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.map.get_index_of(name)
    }

    pub fn get(&self, index: Option<usize>) -> &OperDefTab {
        match index {
            Some(index) => match self.map.get_index(index) {
                Some((_, tab)) => tab,
                None => &EMPTY_OPER_DEF_TAB,
            },
            None => &EMPTY_OPER_DEF_TAB,
        }
    }

    /// Accepts Term
    ///    'op'(
    ///         oper: atom | func(arg: atom | '='(name: atom, default: term)),...),
    ///         type: 'fun' | 'prefix' | 'infix' | 'postfix',
    ///         prec: 0(min)..1200(max), % must be 0 for fixity = 'none'
    ///         assoc: 'none' | 'left' | 'right',
    ///         rename_to: 'none' | some( new_name: atom ),
    ///         embed_type = 'false' | 'true',
    ///    )
    pub fn define_oper(&mut self, arena: &Arena, op: Term) -> Result<()> {
        const BOOLS: &[&str] = &["false", "true"];

        let (_, [oper, fixity, prec, assoc, rename_to, embed_fixity]) =
            op.unpack_func(arena, &["op"])?;

        let (functor, args) = oper.unpack_func_any(arena, &[])?;
        let name = functor.atom_name(arena)?;

        let fixity = Fixity::try_from(fixity.unpack_atom(arena, Fixity::STRS)?)?;
        let prec = prec.unpack_int(arena)?.try_into()?;
        let assoc = Assoc::try_from(assoc.unpack_atom(arena, Assoc::STRS)?)?;
        let embed_fixity = embed_fixity.unpack_atom(arena, BOOLS)? == "true";

        let args = args
            .into_iter()
            .map(|arg| {
                Ok(match arg.view(arena)? {
                    View::Atom(name) => OperArg {
                        name: String::from(name),
                        default: None,
                    },
                    View::Func(ar, _, _) => {
                        let (_, [name, term]) = arg.unpack_func(ar, &["="])?;
                        OperArg {
                            name: String::from(name.atom_name(ar)?),
                            default: Some(term),
                        }
                    }
                    _ => bail!("oper arg must be an atom or =(atom, term) in {:?}", name),
                })
            })
            .collect::<Result<Vec<_>>>()?;

        let required_arity = OperDef::required_arity(fixity);
        if args.len() < required_arity {
            bail!(
                "operator {:?} requires at least {} argument(s)",
                name,
                required_arity
            );
        }

        if args[..required_arity].iter().any(|x| x.default.is_some()) {
            bail!("defaults are not allowed for required operator arguments");
        }

        let unique_arg_names: HashSet<_> = args.iter().map(|x| &x.name).cloned().collect();
        if unique_arg_names.len() != args.len() {
            bail!("duplicate arguments in {:?}", name);
        }

        let rename_to = match rename_to.view(arena)? {
            View::Atom("none") => None,
            View::Func(ar, _, _) => {
                let (_, [rename_to]) = rename_to.unpack_func(ar, &["some"])?;
                Some(rename_to)
            }
            _ => bail!("rename_to must be 'none' | some(atom)"),
        };

        if matches!(fixity, Fixity::Fun) && prec != NON_OPER_PREC {
            bail!("{:?} must be assigned precedence 0", name);
        }
        if !matches!(fixity, Fixity::Fun) && (prec < MIN_OPER_PREC || prec > MAX_OPER_PREC) {
            bail!(
                "precedence {} is out of range for operator {:?} with type {:?} (expected {}–{})",
                prec,
                name,
                fixity,
                MIN_OPER_PREC,
                MAX_OPER_PREC,
            );
        }
        if matches!((fixity, assoc), (Fixity::Prefix, Assoc::Left))
            || matches!((fixity, assoc), (Fixity::Postfix, Assoc::Right))
        {
            bail!(
                "operator {:?} with type {:?} cannot have associativity {:?}",
                name,
                fixity,
                assoc
            );
        }

        // This check is intentionally disabled to preserve compatibility
        // with the behavior of the original C implementation
        #[cfg(false)]
        if matches!((fixity, assoc), (Fixity::Fun, Assoc::Left | Assoc::Right)) {
            bail!(
                "{:?} with type {:?} cannot have associativity {:?}",
                name,
                fixity,
                assoc
            );
        }

        let tab = self
            .map
            .entry(String::from(name))
            .or_insert_with(OperDefTab::new);

        if matches!(fixity, Fixity::Fun) && tab.is_oper() {
            bail!(
                "cannot define {:?} with type {:?}; it is already defined as an operator with a different type",
                name,
                fixity,
            );
        }

        if matches!(fixity, Fixity::Prefix | Fixity::Infix | Fixity::Postfix)
            && tab.tab[Into::<usize>::into(Fixity::Fun)].is_some()
        {
            bail!(
                "cannot define {:?} as an operator with type {:?}; it is already defined with type Fun",
                name,
                fixity,
            );
        }

        if tab[fixity].is_some() {
            bail!("cannot re-define {:?}", name);
        }

        tab[fixity] = Some(OperDef {
            fixity,
            prec,
            assoc,
            rename_to,
            embed_fixity,
            args,
        });

        Ok(())
    }

    pub fn define_opers(&mut self, arena: &Arena, term: Term) -> Result<()> {
        match term.view(arena)? {
            View::List(arena, ts, _) => {
                for t in ts {
                    self.define_oper(arena, *t)?;
                }
            }
            _ => {
                self.define_oper(arena, term)?;
            }
        }
        Ok(())
    }
}
