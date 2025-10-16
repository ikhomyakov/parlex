-- Grammar rules for a simple expression language.
--
-- This file defines the context-free grammar (CFG) productions
-- for a minimal expression language that supports:
--   - Variable assignments
--   - Arithmetic expressions (+, -, *, /)
--   - Unary negation
--   - Parentheses for grouping
--
-- Nonterminals:
--   - Stat : represents a statement
--   - Expr : represents an expression
--
-- Terminals:
--   - ident, number, =, +, -, *, /, (, )
--
-- The grammar is written in production rule form:
--   <label>: <Nonterminal> -> <production>
--
stat1: Stat ->
stat2: Stat -> Expr
stat3: Stat -> ident = Expr
expr1: Expr -> number
expr2: Expr -> ident
expr3: Expr -> Expr + Expr
expr4: Expr -> Expr - Expr
expr5: Expr -> Expr * Expr
expr6: Expr -> Expr / Expr
expr7: Expr -> - Expr
expr8: Expr -> ( Expr )
