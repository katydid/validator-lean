-- LTreeVerbose is a memoizable version of the validation algorithm.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm also avoids using any Monads, so it is verbose compared to a version that would use monads.

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

namespace LTreeVerbose

-- foldLoop is a more readable version of List.foldlM for imperative programmers:
private def foldLoop (deriv: List Expr -> LTree -> Except String (List Expr)) (start: List Expr) (forest: List LTree): Except String (List Expr) := do
  let mut res := start
  for tree in forest do
    match deriv res tree with
    | Except.error err => throw err
    | Except.ok r => res := r
  return res

def deriv (xs: List Expr) (t: LTree): Except String (List Expr) :=
  if List.all xs Expr.unescapable
  then Except.ok xs
  else
    match t with
    | LTree.node label children =>
      let ifExprs: List IfExpr := Enter.enters xs
      -- des == derivatives of enter
      let des : List Expr := IfExpr.evals ifExprs (Token.string label)
      -- dcs == derivatives of children, the ' is for the exception it is wrapped in
      -- see foldLoop for an explanation of what List.foldM does.
      let dcs' : Except String (List Expr) := List.foldlM deriv des children
      match dcs' with
      | Except.error err => Except.error err
      | Except.ok dcs =>
        -- dls == derivatives of leave, the ' is for the exception it is wrapped in
        let dls': Except String (List Expr) := Leave.leaves xs (List.map Expr.nullable dcs)
        match dls' with
        | Except.error err => Except.error err
        | Except.ok dls =>
          Except.ok dls

def derivs (x: Expr) (forest: List LTree): Except String Expr :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldlM deriv [x] forest
  match dxs with
  | Except.error err => Except.error err
  | Except.ok [dx] => Except.ok dx
  | Except.ok _ => Except.error "expected one expression"

def validate (x: Expr) (forest: List LTree): Except String Bool :=
  match derivs x forest with
  | Except.error err => Except.error err
  | Except.ok x' => Except.ok (Expr.nullable x')
