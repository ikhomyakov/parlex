use super::lexer::Token;
use chumsky::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Symbol {
    Term(usize),
    NonTerm(usize),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Production {
    pub label: Option<usize>,
    pub lhs: usize,
    pub rhs: Vec<Symbol>,
}

pub fn parser<'a>() -> impl Parser<'a, &'a [Token], Vec<Production>> {
    let symbol = select! {
        Token::Term(t) => Symbol::Term(t),
        Token::NonTerm(n) => Symbol::NonTerm(n),
    }
    .labelled("symbol");

    let tlist = symbol.repeated().collect::<Vec<_>>();

    let left = select! {
        Token::NonTerm(n) => n,
    }
    .labelled("left");

    let prod_kw = select! { Token::Prod => () }.labelled("Prod");
    let lf = select! { Token::LineFeed => () }.labelled("LineFeed");

    let production_without_label = left
        .then_ignore(prod_kw.clone())
        .then(tlist.clone())
        .then_ignore(lf.clone())
        .map(|(lhs, rhs)| Production {
            label: None,
            lhs,
            rhs,
        })
        .map(Some);

    let production_with_label = select! { Token::ProdLabel(l) => l }
        .then(left)
        .then_ignore(prod_kw)
        .then(tlist)
        .then_ignore(lf.clone())
        .map(|((label, lhs), rhs)| Production {
            label: Some(label),
            lhs,
            rhs,
        })
        .map(Some);

    let empty_line = lf.map(|_| None::<Production>);

    let production = production_with_label
        .or(production_without_label)
        .or(empty_line);

    let productions = production
        .repeated()
        .collect::<Vec<_>>()
        .map(|items| items.into_iter().flatten().collect::<Vec<_>>());

    productions
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_production() {
        let tokens = vec![
            Token::ProdLabel(0),
            Token::NonTerm(1),
            Token::Prod,
            Token::Term(2),
            Token::NonTerm(3),
            Token::LineFeed,
        ];
        let prods = parser().parse(&tokens).unwrap();
        assert_eq!(prods.len(), 1);
        let p = &prods[0];
        assert_eq!(p.label, Some(0));
        assert_eq!(p.lhs, 1);
        assert_eq!(p.rhs, vec![Symbol::Term(2), Symbol::NonTerm(3)]);
    }

    #[test]
    fn empty_line_skipped() {
        let tokens = vec![Token::LineFeed];
        let prods = parser().parse(&tokens).unwrap();
        assert!(prods.is_empty());
    }

    #[test]
    fn multiple_productions() {
        let tokens = vec![
            Token::ProdLabel(10),
            Token::NonTerm(0),
            Token::Prod,
            Token::LineFeed, // empty rhs
            Token::ProdLabel(11),
            Token::NonTerm(2),
            Token::Prod,
            Token::Term(5),
            Token::LineFeed,
        ];
        let prods = parser().parse(&tokens).unwrap();
        assert_eq!(prods.len(), 2);
        assert_eq!(prods[0].label, Some(10));
        assert_eq!(prods[0].lhs, 0);
        assert!(prods[0].rhs.is_empty());
        assert_eq!(prods[1].label, Some(11));
        assert_eq!(prods[1].lhs, 2);
        assert_eq!(prods[1].rhs, vec![Symbol::Term(5)]);
    }
}
