-- LTreeConcise is a memoizable version of the validation algorithm.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

namespace LTreeConcise

def deriv (xs: List Expr) (t: LTree): Except String (List Expr) := do
  if List.all xs Expr.unescapable
  then return xs
  else
    match t with
    | LTree.node label children =>
      let ifExprs: List IfExpr := Enter.enters xs
      -- des == derivatives of enter
      let des : List Expr := IfExpr.evals ifExprs (Token.string label)
      -- cdcs == compressed derivatives of children
      let dcs <- List.foldlM deriv des children
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

def run (x: Expr) (t: LTree): Except String Bool :=
  validate x [t]

#guard run
  Expr.emptyset
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (LTree.node "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (LTree.node "a" [LTree.node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (LTree.node "a" [LTree.node "b" []]) =
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
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" []]) =
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
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok true
