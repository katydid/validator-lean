-- LTreeConciseCompress is a memoizable version of the validation algorithm.
-- On top of LTreeConcise it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

namespace LTreeConciseCompress

def deriv (xs: List Expr) (t: LTree): Except String (List Expr) := do
  if List.all xs Expr.unescapable
  then return xs
  else
    match t with
    | LTree.node label children =>
      let ifExprs: List IfExpr := Enter.enters xs
      -- des == derivatives of enter
      let des : List Expr := IfExpr.evals ifExprs (Token.string label)
      -- NEW: compress
      -- cdes compressed derivatives of enter
      let (cdes, indices) <- Compress.compress des
      -- cdcs == compressed derivatives of children
      let cdcs <- List.foldlM deriv cdes children
      -- NEW: expand
      let dcs <- Compress.expand indices cdcs
      -- dls == derivatives of leave, the ' is for the exception it is wrapped in
      Leave.leaves xs (List.map Expr.nullable dcs)

def derivs (x: Expr) (forest: List LTree): Except String Expr := do
  let dxs <- List.foldlM deriv [x] forest
  match dxs with
  | [dx] => return dx
  | _ => throw "expected one expression"

def validate (x: Expr) (forest: List LTree): Except String Bool := do
  let dx <- derivs x forest
  return Expr.nullable dx
