-- ImperativeCompress is a memoizable version of the validation algorithm.
-- On top of ImperativeCompress it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm also avoids using any Monads, so it is verbose compared to a version that would use monads.

import Validator.Parser.ParseTree

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter

import Validator.Learning.ImperativeLeave

namespace ImperativeCompress

-- deriv is the same as ImperativeBasic's deriv function, except that it includes the use of the compress and expand functions.
def derive (xs: List Expr) (t: ParseTree): Except String (List Expr) :=
  if List.all xs Expr.unescapable
  then Except.ok xs
  else
    match t with
    | ParseTree.node label children =>
      let ifexprs: List IfExpr := Enter.deriveEnter xs
      let childxs: List Expr := IfExpr.evals ifexprs label
      -- cchildxs' = compressed expressions to evaluate on children. The ' is for the exception it is wrapped in.
      let cchildxs' : Except String ((List Expr) × Compress.Indices) := Compress.compress childxs
      match cchildxs' with
      | Except.error err => Except.error err
      | Except.ok (cchildxs, indices) =>
      -- cdchildxs = compressed derivatives of children. The ' is for the exception it is wrapped in.
      -- see foldLoop for an explanation of what List.foldM does.
      let cdchildxs' : Except String (List Expr) := List.foldlM derive cchildxs children
      match cdchildxs' with
      | Except.error err => Except.error err
      | Except.ok cdchildxs =>
      -- dchildxs = uncompressed derivatives of children. The ' is for the exception it is wrapped in.
      let dchildxs' := Compress.expand indices cdchildxs
      match dchildxs' with
      | Except.error err => Except.error err
      | Except.ok dchildxs =>
      -- dxs = derivatives of xs. The ' is for the exception it is wrapped in.
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
