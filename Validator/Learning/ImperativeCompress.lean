-- ImperativeCompress is a memoizable version of the validation algorithm.
-- On top of ImperativeCompress it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm also avoids using any Monads, so it is verbose compared to a version that would use monads.

import Validator.Std.Except

import Validator.Parser.ParseTree
import Validator.Parser.TokenTree

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter
import Validator.Learning.ImperativeLeave

namespace ImperativeCompress

-- deriv is the same as ImperativeBasic's deriv function, except that it includes the use of the compress and expand functions.
def derive [DecidableEq α] (xs: Exprs α) (t: ParseTree α): Except String (Exprs α) :=
  if List.all xs Expr.unescapable
  then Except.ok xs
  else
    match t with
    | ParseTree.mk label children =>
      let ifexprs: IfExprs α := Enter.deriveEnter xs
      let childxs: Exprs α := IfExpr.evals ifexprs label
      -- cchildxs' = compressed expressions to evaluate on children. The ' is for the exception it is wrapped in.
      let cchildxs' : Except String ((Exprs α) × Compress.Indices) := Compress.compress childxs
      match cchildxs' with
      | Except.error err => Except.error err
      | Except.ok (cchildxs, indices) =>
      -- cdchildxs = compressed derivatives of children. The ' is for the exception it is wrapped in.
      -- see foldLoop for an explanation of what List.foldM does.
      let cdchildxs' : Except String (Exprs α) := List.foldlM derive cchildxs children
      match cdchildxs' with
      | Except.error err => Except.error err
      | Except.ok cdchildxs =>
      -- dchildxs = uncompressed derivatives of children. The ' is for the exception it is wrapped in.
      let dchildxs' := Compress.expand indices cdchildxs
      match dchildxs' with
      | Except.error err => Except.error err
      | Except.ok dchildxs =>
      -- dxs = derivatives of xs. The ' is for the exception it is wrapped in.
      let dxs': Except String (Exprs α) := ImperativeLeave.deriveLeave xs (List.map Expr.nullable dchildxs)
      match dxs' with
      | Except.error err => Except.error err
      | Except.ok dxs => Except.ok dxs

def derivs [DecidableEq α] (x: Expr α) (forest: ParseForest α): Except String (Expr α) :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldlM derive [x] forest
  match dxs with
  | Except.error err => Except.error err
  | Except.ok [dx] => Except.ok dx
  | Except.ok _ => Except.error "expected one expression"

def validate [DecidableEq α] (x: Expr α) (forest: ParseForest α): Except String Bool :=
  match derivs x forest with
  | Except.error err => Except.error err
  | Except.ok x' => Except.ok (Expr.nullable x')

def run [DecidableEq α] (x: Expr α) (t: ParseTree α): Except String Bool :=
  validate x [t]

open TokenTree (node)

#guard run
  Expr.emptyset
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (node "a" [node "b" []]) =
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
  (node "a" [node "b" [], node "c" []]) =
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
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true
