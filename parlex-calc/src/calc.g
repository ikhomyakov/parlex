-- Grammar rules for a simple expression language.
--
-- NOTE:
--   In real-world lexers, comments are usually **skipped** before parsing and can appear anywhere.
--   Here, they’re deliberately **included in the grammar** to demonstrate span merging. This
--   **toy example** restricts comments to a single position before each statement and showcases
--   span tracking and typical **expression-operator shift/reduce conflicts**.
--
-- This file defines the context-free grammar productions
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
--   In production rules, **terminals** conventionally start with *lowercase* letters,
--   while **nonterminals** begin with *uppercase* letters.

stat1: Stat ->
stat2: Stat -> comment Stat
stat3: Stat -> Expr
stat4: Stat -> ident = Expr
expr1: Expr -> number
expr2: Expr -> ident
expr3: Expr -> Expr + Expr
expr4: Expr -> Expr - Expr
expr5: Expr -> Expr * Expr
expr6: Expr -> Expr / Expr
expr7: Expr -> - Expr
expr8: Expr -> ( Expr )
