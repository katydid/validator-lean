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

def deriv (xs: List Expr) (t: ParseTree): Except String (List Expr) :=
  if List.all xs Expr.unescapable
  then Except.ok xs
  else
    match t with
    | ParseTree.node label children =>
      let ifExprs: List IfExpr := Enter.enters xs
      -- des == derivatives of enter
      let des : List Expr := IfExpr.evals ifExprs label
      -- dcs == derivatives of children, the ' is for the exception it is wrapped in
      -- see foldLoop for an explanation of what List.foldM does.
      let dcs' : Except String (List Expr) := List.foldlM deriv des children
      match dcs' with
      | Except.error err => Except.error err
      | Except.ok dcs =>
        -- dls == derivatives of leave, the ' is for the exception it is wrapped in
        let dls': Except String (List Expr) := ImperativeLeave.leaves xs (List.map Expr.nullable dcs)
        match dls' with
        | Except.error err => Except.error err
        | Except.ok dls => Except.ok dls

def derivs (x: Expr) (forest: List ParseTree): Except String Expr :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldlM deriv [x] forest
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
