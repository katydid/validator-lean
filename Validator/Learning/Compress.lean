-- Compress is a memoizable version of the validation algorithm.
-- On top of Basic it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except

import Validator.Std.ParseTree
import Validator.Parser.TokenTree

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter
import Validator.Derive.Leave

namespace Compress

-- deriv is the same as Basic's deriv function, except that it includes the use of the compress and expand functions.
def derive [DecidableEq α] (xs: Exprs α) (t: ParseTree α): Except String (Exprs α) := do
  if List.all xs Expr.unescapable
  then return xs
  else
    match t with
    | ParseTree.mk label children =>
      let ifexprs: IfExprs α := Enter.deriveEnter xs
      let childxs: Exprs α := IfExpr.evals ifexprs label
      -- cchildxs = compressed expressions to evaluate on children.
      let (cchildxs, indices) <- Compress.compress childxs
      -- cdchildxs = compressed derivatives of children.
      let cdchildxs <- List.foldlM derive cchildxs children
      -- dchildxs = uncompressed derivatives of children.
      let dchildxs <- Compress.expand indices cdchildxs
      Leave.deriveLeave xs (List.map Expr.nullable dchildxs)

def derivs [DecidableEq α] (x: Expr α) (forest: ParseForest α): Except String (Expr α) := do
  let dxs <- List.foldlM derive [x] forest
  match dxs with
  | [dx] => return dx
  | _ => throw "expected one expression"

def validate [DecidableEq α] (x: Expr α) (forest: ParseForest α): Except String Bool := do
  let dx <- derivs x forest
  return Expr.nullable dx

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
