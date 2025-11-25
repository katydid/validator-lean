-- Basic is a memoizable version of the validation algorithm.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Language

import Validator.Derive.Enter
import Validator.Derive.Leave

namespace Basic

def derive {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (xs: Rules n (Pred α) l) (t: Hedge.Node α): Rules n (Pred α) l :=
  if List.all xs.toList Regex.unescapable
  then xs
  else
    match t with
    | Hedge.Node.mk label children =>
      -- enters is one of our two new memoizable functions.
      let ifExprs: IfExprs n α (Symbol.nums xs) := Enter.deriveEnter xs
      -- childxs = expressions to evaluate on children.
      let childxs: Rules n (Pred α) (Symbol.nums xs) := IfExpr.evals g ifExprs label
      -- dchildxs = derivatives of children.
      let dchildxs := List.foldl (derive g) childxs children
      -- leaves is the other one of our two new memoizable functions.
      Leave.deriveLeaves xs (List.Vector.map Rule.nullable dchildxs)

def derivs {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (x: Rule n (Pred α)) (hedge: Hedge α): Rule n (Pred α) :=
  let dxs := List.foldl (derive g) (List.Vector.cons x List.Vector.nil) hedge
  dxs.head

def validate {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (x: Rule n (Pred α)) (hedge: Hedge α): Bool :=
  let dx := derivs g x hedge
  Rule.nullable dx

def run {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (t: Hedge.Node α): Bool :=
  validate g g.start [t]

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]])
  = false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [])
  = true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []])
  = false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = true

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []])
  = true

#guard run
  (Grammar.mk (n := 3)
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
  (node "a" [node "b" [], node "c" [node "d" []]])
  = true
