-- ImperativeBasic is a memoizable version of the validation algorithm.
-- This is intended to be as approachable as possible to imperative programmers and avoids using Monads.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex

import Validator.Derive.Enter
import Validator.Learning.ImperativeLeave

namespace ImperativeBasic

-- foldLoop is a more readable version of List.foldlM for imperative programmers:
private def foldLoop (deriv: Rules μ α Pred -> Hedge.Node α -> Except String (Rules μ α Pred)) (start: Rules μ α Pred) (hedge: Hedge α): Except String (Rules μ α Pred) := do
  let mut res := start
  for tree in hedge do
    match deriv res tree with
    | Except.error err => throw err
    | Except.ok r => res := r
  return res

def derive [DecidableEq α] (g: Grammar μ α Pred) (xs: Rules μ α Pred) (tree: Hedge.Node α): Except String (Rules μ α Pred) :=
  -- If all expressions are unescapable, then simply return without look at the input tree.
  -- An example of an unescapable expression is emptyset, since its derivative is always emptyset, no matter the input.
  if List.all xs Regex.unescapable
  then Except.ok xs
  else
    -- Desconstruct the tree to retrieve its label and children
    match tree with
    | Hedge.Node.mk label children =>
      -- enters is one of our two new memoizable functions.
      let ifexprs: IfExprs μ α := Enter.deriveEnter xs
      -- childxs = expressions to evaluate on children.
      let childxs: Rules μ α Pred := IfExpr.evals g ifexprs label
      -- dchildxs = derivatives of children. The ' is for the exception it is wrapped in.
      -- see foldLoop for an explanation of what List.foldM does.
      let dchildxs': Except String (Rules μ α Pred) := List.foldlM (derive g) childxs children
      match dchildxs' with
      | Except.error err => Except.error err
      | Except.ok dchildxs =>
      -- dxs = derivatives of xs. The ' is for the exception it is wrapped in.
      -- leaves is the other one of our two new memoizable functions.
      let dxs': Except String (Rules μ α Pred) := ImperativeLeave.deriveLeave xs (List.map Regex.nullable dchildxs)
      match dxs' with
      | Except.error err => Except.error err
      | Except.ok dxs => Except.ok dxs

def derivs [DecidableEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred) (hedge: Hedge α): Except String (Rule μ α Pred) :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldlM (derive g) [x] hedge
  match dxs with
  | Except.error err => Except.error err
  | Except.ok [dx] => Except.ok dx
  | Except.ok _ => Except.error "expected one expression"

def validate [DecidableEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred) (hedge: Hedge α): Except String Bool :=
  match derivs g x hedge with
  | Except.error err => Except.error err
  | Except.ok x' => Except.ok (Rule.nullable x')

def run [DecidableEq α] (g: Grammar μ α Pred) (t: Hedge.Node α): Except String Bool :=
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
