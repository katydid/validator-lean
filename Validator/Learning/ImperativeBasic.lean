-- ImperativeBasic is a memoizable version of the validation algorithm.
-- This is intended to be as approachable as possible to imperative programmers and avoids using Monads.

import Validator.Parser.ParseTree

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter

import Validator.Learning.ImperativeLeave

namespace ImperativeBasic

-- foldLoop is a more readable version of List.foldlM for imperative programmers:
private def foldLoop (deriv: List Expr -> ParseTree -> Except String (List Expr)) (start: List Expr) (forest: List ParseTree): Except String (List Expr) := do
  let mut res := start
  for tree in forest do
    match deriv res tree with
    | Except.error err => throw err
    | Except.ok r => res := r
  return res

def derive (xs: List Expr) (tree: ParseTree): Except String (List Expr) :=
  -- If all expressions are unescapable, then simply return without look at the input tree.
  -- An example of an unescapable expression is emptyset, since its derivative is always emptyset, no matter the input.
  if List.all xs Expr.unescapable
  then Except.ok xs
  else
    -- Desconstruct the tree to retrieve its label and children
    match tree with
    | ParseTree.node label children =>
      -- enters is one of our two new memoizable functions.
      let ifexprs: List IfExpr := Enter.deriveEnter xs
      -- childxs = expressions to evaluate on children.
      let childxs: List Expr := IfExpr.evals ifexprs label
      -- dchildxs = derivatives of children. The ' is for the exception it is wrapped in.
      -- see foldLoop for an explanation of what List.foldM does.
      let dchildxs': Except String (List Expr) := List.foldlM derive childxs children
      match dchildxs' with
      | Except.error err => Except.error err
      | Except.ok dchildxs =>
      -- dxs = derivatives of xs. The ' is for the exception it is wrapped in.
      -- leaves is the other one of our two new memoizable functions.
      let dxs': Except String (List Expr) := ImperativeLeave.deriveLeave xs (List.map Expr.nullable dchildxs)
      match dxs' with
      | Except.error err => Except.error err
      | Except.ok dxs => Except.ok dxs

def derivs (x: Expr) (forest: List ParseTree): Except String Expr :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldlM derive [x] forest
  match dxs with
  | Except.error err => Except.error err
  | Except.ok [dx] => Except.ok dx
  | Except.ok _ => Except.error "expected one expression"

def validate (x: Expr) (forest: List ParseTree): Except String Bool :=
  match derivs x forest with
  | Except.error err => Except.error err
  | Except.ok x' => Except.ok (Expr.nullable x')

def run (x: Expr) (t: ParseTree): Except String Bool :=
  validate x [t]

-- Tests
-- Lean can use #guard to run these tests at compile time.

open ParseTree (field)

#guard run
  Expr.emptyset
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" [field "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (field "a" [field "b" []]) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        Expr.epsilon
      )
    )
  )
  (field "a" [field "b" [], field "c" []]) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        (Expr.tree (Pred.eq (Token.string "d"))
          Expr.epsilon
        )
      )
    )
  )
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok true
