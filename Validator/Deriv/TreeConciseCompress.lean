-- TreeConciseCompress is a memoizable version of the validation algorithm.
-- On top of TreeConcise it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Parser.ParseTree

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

namespace TreeConciseCompress

def deriv (xs: List Expr) (t: ParseTree): Except String (List Expr) := do
  if List.all xs Expr.unescapable
  then return xs
  else
    match t with
    | ParseTree.node label children =>
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

def derivs (x: Expr) (forest: List ParseTree): Except String Expr := do
  let dxs <- List.foldlM deriv [x] forest
  match dxs with
  | [dx] => return dx
  | _ => throw "expected one expression"

def validate (x: Expr) (forest: List ParseTree): Except String Bool := do
  let dx <- derivs x forest
  return Expr.nullable dx

def run (x: Expr) (t: ParseTree): Except String Bool :=
  validate x [t]

#guard run
  Expr.emptyset
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" [ParseTree.node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (ParseTree.node "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (ParseTree.node "a" [ParseTree.node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (ParseTree.node "a" [ParseTree.node "b" []]) =
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
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" []]) =
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
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" [ParseTree.node "d" []]]) =
  Except.ok true
