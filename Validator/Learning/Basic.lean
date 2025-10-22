-- Basic is a memoizable version of the validation algorithm.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Compress
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Language

import Validator.Derive.Enter
import Validator.Derive.Leave

namespace Basic

def derive {α: Type} [DecidableEq α] (g: Grammar μ α Pred) (xs: Rules μ α Pred) (t: Hedge.Node α): Except String (Rules μ α Pred) := do
  if List.all xs Regex.unescapable
  then Except.ok xs
  else
    match t with
    | Hedge.Node.mk label children =>
      -- enters is one of our two new memoizable functions.
      let ifExprs: IfExprs μ α := Enter.deriveEnter xs
      -- childxs = expressions to evaluate on children.
      let childxs: Rules μ α Pred := IfExpr.evals g ifExprs label
      -- dchildxs = derivatives of children.
      let dchildxs <- List.foldlM (derive g) childxs children
      -- leaves is the other one of our two new memoizable functions.
      Leave.deriveLeaveM xs (List.map Rule.nullable dchildxs)

def derivs {α: Type} [DecidableEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred) (hedge: Hedge α): Except String (Rule μ α Pred) := do
  let dxs <- List.foldlM (derive g) [x] hedge
  match dxs with
  | [dx] => return dx
  | _ => throw "expected one expression"

def validate {α: Type} [DecidableEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred) (hedge: Hedge α): Except String Bool := do
  let dx <- derivs g x hedge
  return Rule.nullable dx

def run {α: Type} [DecidableEq α] (g: Grammar μ α Pred) (t: Hedge.Node α): Except String Bool :=
  validate g g.start [t]

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Grammar.mk (μ := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.eq (Token.string "d"), 1))
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true
