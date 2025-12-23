-- Basic is a memoizable version of the validation algorithm.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except
import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Parser.TokenTree

import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr
import Validator.Regex.Language
import Validator.Pred.AnyEq

import Validator.Regex.Enter
import Validator.Regex.LeaveSmart

namespace Basic

def derive {α: Type}
  (G: Hedge.Grammar n φ) (Φ : φ → α → Bool)
  (xs: Hedge.Grammar.Rules n φ l) (t: Hedge.Node α): Hedge.Grammar.Rules n φ l :=
  if List.all xs.toList Regex.unescapable
  then xs
  else
    -- enters is one of our two new memoizable functions.
    let ifExprs: Hedge.Grammar.Symbols n φ (Regex.Symbol.nums xs) := Regex.Enter.enters xs
    match t with
    | Hedge.Node.mk label children =>
      -- childxs = expressions to evaluate on children.
      let childxs: Hedge.Grammar.Rules n φ (Regex.Symbol.nums xs) := Hedge.Grammar.evalifs G Φ ifExprs label
      -- dchildxs = derivatives of children.
      let dchildxs: Hedge.Grammar.Rules n φ (Regex.Symbol.nums xs) := List.foldl (derive G Φ) childxs children
      let ns: Vec Bool (Regex.Symbol.nums xs) := Vec.map dchildxs Hedge.Grammar.Rule.null
      -- leaves is the other one of our two new memoizable functions.
      let lchildxs: Hedge.Grammar.Rules n φ l := Regex.LeaveSmart.leaves xs ns
      lchildxs

def derivs {α: Type}
  (G: Hedge.Grammar n φ) (Φ : φ → α → Bool)
  (x: Hedge.Grammar.Rule n φ) (hedge: Hedge α): Hedge.Grammar.Rule n φ :=
  let dxs := List.foldl (derive G Φ) (#vec[x]) hedge
  dxs.head

def validate {α: Type}
  (G: Hedge.Grammar n φ) (Φ : φ → α → Bool)
  (x: Hedge.Grammar.Rule n φ) (hedge: Hedge α): Bool :=
  let dx := derivs G Φ x hedge
  Hedge.Grammar.Rule.null dx

def run {α: Type} [DecidableEq α] (G: Hedge.Grammar n (AnyEq.Pred α)) (t: Hedge.Node α): Bool :=
  validate G AnyEq.Pred.evalb G.start [t]

-- Tests

open TokenTree (node)

#guard run
  (Hedge.Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]])
  = false

#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [])
  = true

#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []])
  = false

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = true

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []])
  = true

#guard run
  (Hedge.Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq (Token.string "d"), 1))
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = true
