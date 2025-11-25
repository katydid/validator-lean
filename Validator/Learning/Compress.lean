-- Compress is a memoizable version of the validation algorithm.
-- On top of Basic it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Compress
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex

import Validator.Derive.Enter
import Validator.Derive.Leave

namespace Compress

-- deriv is the same as Basic's deriv function, except that it includes the use of the compress and expand functions.
def derive [DecidableEq α] (g: Grammar μ α Pred) (xs: Rules μ α Pred ν) (t: Hedge.Node α): Rules μ α Pred ν :=
  if List.all xs.toList Regex.unescapable
  then xs
  else
    match t with
    | Hedge.Node.mk label children =>
      let ifexprs: IfExprs μ α (Symbol.nums xs) := Enter.deriveEnter xs
      let childxs: Rules μ α Pred (Symbol.nums xs) := IfExpr.evals g ifexprs label
      -- cchildxs = compressed expressions to evaluate on children.
      let ⟨n, cchildxs, indices⟩ := Compress.compress childxs
      -- cdchildxs = compressed derivatives of children.
      let cdchildxs := List.foldl (derive g) cchildxs children
      -- dchildxs = uncompressed derivatives of children.
      let dchildxs := Compress.expand indices cdchildxs
      Leave.deriveLeaves xs (List.Vector.map Rule.nullable dchildxs)

def derivs [DecidableEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred) (hedge: Hedge α): Rule μ α Pred :=
  let dxs := List.foldl (derive g) (List.Vector.cons x List.Vector.nil) hedge
  dxs.head

def validate [DecidableEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred) (hedge: Hedge α): Bool :=
  let dx := derivs g x hedge
  Rule.nullable dx

def run [DecidableEq α] (g: Grammar μ α Pred) (t: Hedge.Node α): Bool :=
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
