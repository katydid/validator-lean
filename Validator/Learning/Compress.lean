-- Compress is a memoizable version of the validation algorithm.
-- On top of Basic it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except
import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Parser.TokenTree

import Validator.Expr.Compress
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex

import Validator.Derive.Enter
import Validator.Derive.Leave

namespace Compress

-- deriv is the same as Basic's deriv function, except that it includes the use of the compress and expand functions.
def derive [DecidableEq φ]
  (g: Grammar n φ) (Φ : φ → α → Prop) [DecidableRel Φ]
  (xs: Rules n φ l) (t: Hedge.Node α): Rules n φ l :=
  if List.all xs.toList Regex.unescapable
  then xs
  else
    match t with
    | Hedge.Node.mk label children =>
      let ifexprs: IfExprs n φ (Symbol.nums xs) := Enter.deriveEnter xs
      let childxs: Rules n φ (Symbol.nums xs) := IfExpr.evals g Φ ifexprs label
      -- cchildxs = compressed expressions to evaluate on children.
      let ⟨n, cchildxs, indices⟩ := Compress.compress childxs
      -- cdchildxs = compressed derivatives of children.
      let cdchildxs := List.foldl (derive g Φ) cchildxs children
      -- dchildxs = uncompressed derivatives of children.
      let dchildxs := Compress.expand indices cdchildxs
      Leave.deriveLeaves xs (Vec.map dchildxs Rule.nullable)

def derivs [DecidableEq φ]
  (g: Grammar n φ) (Φ : φ → α → Prop) [DecidableRel Φ]
  (x: Rule n φ) (hedge: Hedge α): Rule n φ :=
  let dxs := List.foldl (derive g Φ) (Vec.cons x Vec.nil) hedge
  dxs.head

def validate [DecidableEq φ]
  (g: Grammar n φ) (Φ : φ → α → Prop) [DecidableRel Φ]
  (x: Rule n φ) (hedge: Hedge α): Bool :=
  let dx := derivs g Φ x hedge
  Rule.nullable dx

def run [DecidableEq α] (g: Grammar n (Pred α)) (t: Hedge.Node α): Bool :=
  validate g Pred.eval g.start [t]

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]])
  = false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [])
  = true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []])
  = false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = true

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
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
    #vec[
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
