-- LTreeVerboseCompress is a memoizable version of the validation algorithm.
-- On top of LTreeVerbose it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm also avoids using any Monads, so it is verbose compared to a version that would use monads.

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

namespace LTreeVerboseCompress

def deriv (xs: List Expr) (t: LTree): Except String (List Expr) :=
  if List.all xs Expr.unescapable
  then Except.ok xs
  else
    match t with
    | LTree.node label children =>
      let ifExprs: List IfExpr := Enter.enters xs
      -- des == derivatives of enter
      let des : List Expr := List.map (fun x => IfExpr.eval x (Token.string label)) ifExprs
      -- NEW: compress
      -- cdes compressed derivatives of enter
      let cdes' : Except String ((List Expr) × Compress.Indices) := Compress.compress des
      match cdes' with
      | Except.error err => Except.error err
      | Except.ok (cdes, indices) =>
        -- cdcs == compressed derivatives of children, the ' is for the exception it is wrapped in
        -- see foldLoop for an explanation of what List.foldM does.
        let cdcs' : Except String (List Expr) := List.foldlM deriv cdes children
        match cdcs' with
        | Except.error err => Except.error err
        | Except.ok cdcs =>
          -- NEW: expand
          let dcs' := Compress.expand indices cdcs
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
