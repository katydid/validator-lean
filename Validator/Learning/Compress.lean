-- Compress is a memoizable version of the validation algorithm.
-- On top of Basic it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except

import Validator.Parser.ParseTree

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter
import Validator.Derive.Leave

namespace Compress

-- deriv is the same as Basic's deriv function, except that it includes the use of the compress and expand functions.
def derive (xs: List Expr) (t: ParseTree): Except String (List Expr) := do
  if List.all xs Expr.unescapable
  then return xs
  else
    match t with
    | ParseTree.mk label children =>
      let ifexprs: List IfExpr := Enter.deriveEnter xs
      let childxs: List Expr := IfExpr.evals ifexprs label
      -- cchildxs = compressed expressions to evaluate on children.
      let (cchildxs, indices) <- Compress.compress childxs
      -- cdchildxs = compressed derivatives of children.
      let cdchildxs <- List.foldlM derive cchildxs children
      -- dchildxs = uncompressed derivatives of children.
      let dchildxs <- Compress.expand indices cdchildxs
      Leave.deriveLeave xs (List.map Expr.nullable dchildxs)

def derivs (x: Expr) (forest: List ParseTree): Except String Expr := do
  let dxs <- List.foldlM derive [x] forest
  match dxs with
  | [dx] => return dx
  | _ => throw "expected one expression"

def validate (x: Expr) (forest: List ParseTree): Except String Bool := do
  let dx <- derivs x forest
  return Expr.nullable dx

def run (x: Expr) (t: ParseTree): Except String Bool :=
  validate x [t]

open ParseTree (node)

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
