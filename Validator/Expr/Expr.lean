import Init.Control.State

import Validator.Parser.Hint
import Validator.Parser.LTree
import Validator.Parser.Parser
import Validator.Parser.Stack
import Validator.Parser.Token

namespace Expr

open List

def Predicate := Token -> Bool

inductive Expr where
  | emptyset
  | epsilon
  | tree (labelPred: Predicate) (childrenExpr: Expr)
  | or (y z: Expr)
  | concat (y z: Expr)
  | star (y: Expr)

def nullable (x: Expr): Bool :=
  match x with
  | Expr.emptyset => False
  | Expr.epsilon => True
  | Expr.tree _ _ => False
  | Expr.or y z => nullable y || nullable z
  | Expr.concat y z => nullable y && nullable z
  | Expr.star _ => True

partial def derive (x: Expr) (t: LTree): Expr :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childrenExpr =>
    let childResExpr := List.foldl derive childrenExpr (children t)
    if labelPred (Token.string (label t))
    then
      if nullable childResExpr
      then Expr.epsilon
      else Expr.emptyset
    else Expr.emptyset
  | Expr.or y z => Expr.or (derive y t) (derive z t)
  | Expr.concat y z =>
    if nullable y
    then Expr.or (Expr.concat (derive y t) z) (derive z t)
    else Expr.concat (derive y t) z
  | Expr.star y => Expr.concat (derive y t) (Expr.star y)

partial def validate (x: Expr) (forest: List LTree): Bool :=
  nullable (List.foldl derive x forest)

inductive IfExpr where
  | mk (cnd: Predicate) (thn: Expr) (els: Expr)

-- https://github.com/katydid/katydid-haskell/blob/master/src/Data/Katydid/Relapse/Derive.hs

def dEnter (x: Expr) (res: List IfExpr := []): List IfExpr :=
  match x with
  | Expr.emptyset => res
  | Expr.epsilon => res
  | Expr.tree p y => (IfExpr.mk p y Expr.emptyset) :: res
  | Expr.or y z => dEnter y (dEnter z res)
  | Expr.concat y z =>
    if nullable y
    then dEnter y (dEnter z res)
    else dEnter y res
  | Expr.star y => dEnter y res

def dLeave (x: Expr) (ns: List Bool): Except String (Expr × List Bool) :=
  match x with
  | Expr.emptyset => Except.ok (Expr.emptyset, ns)
  | Expr.epsilon => Except.ok (Expr.epsilon, ns)
  | Expr.tree _ _ =>
    match ns with
    | [] => Except.error "wtf"
    | (null::ns') =>
      if null
      then Except.ok (Expr.epsilon, ns')
      else Except.ok (Expr.emptyset, ns')
  | Expr.or y z =>
    match dLeave y ns with
    | Except.error e => Except.error e
    | Except.ok (y', ns') =>
      match dLeave z ns' with
      | Except.error e => Except.error e
      | Except.ok (z', ns'') =>
        Except.ok (Expr.or y' z', ns'')
  | Expr.concat y z =>
    if nullable y
    then
      match dLeave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        match dLeave z ns' with
        | Except.error e => Except.error e
        | Except.ok (z', ns'') =>
          Except.ok (Expr.or (Expr.concat y' z) z', ns'')
    else
      match dLeave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        Except.ok (Expr.concat y' z, ns')
  | Expr.star y =>
      match dLeave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        Except.ok (Expr.star y', ns')

-- dLeaves takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def dLeaves (xs: List Expr) (ns: List Bool): Except String (List Expr) :=
  match xs with
  | [] =>
    match ns with
    | [] => Except.ok []
    | _ => Except.error "nulls are left, but there are no expressions to place them in"
  | (x::xs') =>
    let dl: Except String (Expr × List Bool) := dLeave x ns
    match dl with
    | Except.error err => Except.error err
    | Except.ok (dx, tailns) =>
      let dls: Except String (List Expr) := dLeaves xs' tailns
      match dls with
      | Except.error err => Except.error err
      | Except.ok dxs' =>
        Except.ok (dx::dxs')

def unescapable (x: Expr): Bool :=
  match x with
  | Expr.emptyset => true
  | _ => false

def evalIfExpr (ifExpr: IfExpr) (t: Token): Expr :=
  match ifExpr with
  | IfExpr.mk cnd thn els =>
    if cnd t
    then thn
    else els

def deriv (xs: List Expr) (t: LTree): Except String (List Expr) :=
  if all xs unescapable
  then Except.ok xs
  else
    match t with
    | LTree.node label children =>
      let ifExprs: List IfExpr := List.flatten (List.map dEnter xs)
      -- des == derivatives of enter
      let des : List Expr := List.map (fun x => evalIfExpr x (Token.string label)) ifExprs
      -- dcs == derivatives of children, the ' is for the exception it is wrapped in
      let dcs' : Except String (List Expr) := foldlM deriv des children
      match dcs' with
      | Except.error err => Except.error err
      | Except.ok dcs =>
        -- dls == derivatives of leave, the ' is for the exception it is wrapped in
        let dls': Except String (List Expr) := dLeaves xs (map nullable dcs)
        match dls' with
        | Except.error err => Except.error err
        | Except.ok dls =>
          Except.ok dls

def derivs (x: Expr) (forest: List LTree): Except String Expr :=
  let dxs := foldlM deriv [x] forest
  match dxs with
  | Except.error err => Except.error err
  | Except.ok [dx] => Except.ok dx
  | Except.ok _ => Except.error "expected one expression"
