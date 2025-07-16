-- ParserConcise is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a LTree.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

import Validator.Parser.Parser
import Validator.Parser.Hint

import Validator.Parser.LTree

namespace LTreeConcise

def derivEnter' (xs: List Expr) (token: Token): List Expr :=
  let ifExprs: List IfExpr := Enter.enters xs
  IfExpr.evals ifExprs token

def derivLeave' [Monad m] [MonadExcept String m] (xs: List Expr) (cs: List Expr): m (List Expr) :=
  Leave.leaves xs (List.map Expr.nullable cs)

def derivValue' [Monad m] [MonadExcept String m] (xs: List Expr) (token: Token): m (List Expr) :=
  let cs := derivEnter' xs token
  derivLeave' xs cs

def derivValue [Monad m] [MonadExcept String m] [Parser m] (xs: List Expr): m (List Expr) := do
  let token := <- Parser.token
  let dxs := <- derivValue' xs token
  return dxs

partial def deriv [Monad m] [MonadExcept String m] [Parser m] (xs: List Expr) (top: Bool): m (List Expr) := do
  if List.all xs Expr.unescapable then
    Parser.skip
    return xs
  let next := <- Parser.next
  match next with
  | Hint.field =>
    let token := <- Parser.token
    let des := derivEnter' xs token
    let next := <- Parser.next
    let dxs <- match next with
    | Hint.field =>
      throw "unexpected field"
    | Hint.value =>
      let dcs := <- derivValue des
      derivLeave' xs dcs
    | Hint.enter =>
      let dcs := <- deriv des false
      derivLeave' xs dcs
    | Hint.leave =>
      throw "unexpected leave"
    | Hint.eof =>
      throw "unexpected eof"
    deriv dxs false
  | Hint.value =>
    let dxs <- derivValue xs
    deriv dxs false
  | Hint.enter =>
    if top
    then
      let dxs <- deriv xs false
      deriv dxs true
    else
      throw "unexpected enter"
  | Hint.leave =>
    if top
    then throw "unexpected leave"
    else return xs
  | Hint.eof =>
    if top
    then return xs
    else throw "unexpected eof"

partial def derivStart [Monad m] [MonadExcept String m] [Parser m] (xs: List Expr): m (List Expr) := do
  deriv xs true

private def dvalidate [Monad m] [MonadExcept String m] [Parser m] (x: Expr): m Expr := do
  let dxs <- derivStart [x]
  match dxs with
  | [dx] => return dx
  | _ => throw "expected one expression"

def validate [Monad m] [MonadExcept String m] [Parser m] (x: Expr): m Bool := do
  let dx <- dvalidate x
  return Expr.nullable dx

def run (x: Expr) (t: LTree): Except String Bool :=
  LTree.LTreeParser.run (validate x) t

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
