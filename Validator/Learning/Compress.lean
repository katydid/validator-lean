-- Compress is a memoizable version of the validation algorithm.
-- On top of Basic it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter
import Validator.Derive.Leave

namespace Compress

-- deriv is the same as Basic's deriv function, except that it includes the use of the compress and expand functions.
def derive [DecidableEq α] (g: Expr.Grammar μ α) (xs: Exprs μ α) (t: Hedge.Node α): Except String (Exprs μ α) := do
  if List.all xs Expr.unescapable
  then return xs
  else
    match t with
    | Hedge.Node.mk label children =>
      let ifexprs: IfExprs μ α := Enter.deriveEnter xs
      let childxs: Exprs μ α := IfExpr.evals g ifexprs label
      -- cchildxs = compressed expressions to evaluate on children.
      let (cchildxs, indices) <- Compress.compress childxs
      -- cdchildxs = compressed derivatives of children.
      let cdchildxs <- List.foldlM (derive g) cchildxs children
      -- dchildxs = uncompressed derivatives of children.
      let dchildxs <- Compress.expand indices cdchildxs
      Leave.deriveLeaveM xs (List.map Expr.nullable dchildxs)

def derivs [DecidableEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (forest: Hedge α): Except String (Expr μ α) := do
  let dxs <- List.foldlM (derive g) [x] forest
  match dxs with
  | [dx] => return dx
  | _ => throw "expected one expression"

def validate [DecidableEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (forest: Hedge α): Except String Bool := do
  let dx <- derivs g x forest
  return Expr.nullable dx

def run [DecidableEq α] (g: Expr.Grammar μ α) (t: Hedge.Node α): Except String Bool :=
  validate g g.lookup0 [t]

open TokenTree (node)

#guard run
  (Expr.Grammar.singleton Expr.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.tree (Pred.eq (Token.string "b")) 2)
      , Expr.epsilon
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b")) 2)
        (Expr.tree (Pred.eq (Token.string "c")) 2)
      )
      , Expr.epsilon
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 4)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b")) 2)
        (Expr.tree (Pred.eq (Token.string "c")) 3)
      )
      , Expr.epsilon
      , (Expr.tree (Pred.eq (Token.string "d")) 2)
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true
