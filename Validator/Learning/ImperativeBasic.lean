-- ImperativeBasic is a memoizable version of the validation algorithm.
-- This is intended to be as approachable as possible to imperative programmers and avoids using Monads.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex

import Validator.Learning.ImperativeEnter
import Validator.Learning.ImperativeLeave

namespace ImperativeBasic

-- foldLoop is a more readable version of List.foldlM for imperative programmers:
private def foldLoop (deriv: List (Rule n φ) -> Hedge.Node α -> List (Rule n φ)) (start: List (Rule n φ)) (hedge: Hedge α): Id (List (Rule n φ)) := do
  let mut res := start
  for tree in hedge do
    res := deriv res tree
  return res

def derive
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (xs: List (Rule n φ)) (tree: Hedge.Node α): List (Rule n φ) :=
  -- If all expressions are unescapable, then simply return without look at the input tree.
  -- An example of an unescapable expression is emptyset, since its derivative is always emptyset, no matter the input.
  if List.all xs Regex.unescapable
  then xs
  else
    -- Desconstruct the tree to retrieve its label and children
    match tree with
    | Hedge.Node.mk label children =>
      -- enters is one of our two new memoizable functions.
      let ifexprs: List (IfExpr n φ) := ImperativeEnter.deriveEnter xs
      -- childxs = expressions to evaluate on children.
      let childxs: List (Rule n φ) := List.map (fun x => IfExpr.eval g Φ x label) ifexprs
      -- dchildxs = derivatives of children. The ' is for the exception it is wrapped in.
      -- see foldLoop for an explanation of what List.foldM does.
      let dchildxs: List (Rule n φ) := List.foldl (derive g Φ) childxs children
      -- dxs = derivatives of xs. The ' is for the exception it is wrapped in.
      -- leaves is the other one of our two new memoizable functions.
      let dxs: List (Rule n φ) := ImperativeLeave.deriveLeave xs (List.map Regex.nullable dchildxs)
      dxs

def derivs
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (x: Rule n φ) (hedge: Hedge α): Except String (Rule n φ) :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldl (derive g Φ) [x] hedge
  match dxs with
  | [dx] => Except.ok dx
  | _ => Except.error "expected one expression"

def validate
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (x: Rule n φ) (hedge: Hedge α): Except String Bool :=
  match derivs g Φ x hedge with
  | Except.error err => Except.error err
  | Except.ok x' => Except.ok (Rule.nullable x')

def run [DecidableEq α]
  (g: Grammar n (Pred α)) (t: Hedge.Node α): Except String Bool :=
  validate g Pred.eval g.start [t]

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

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
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

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
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true
