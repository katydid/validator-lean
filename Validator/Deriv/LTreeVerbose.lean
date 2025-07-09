-- LTreeVerbose is a memoizable version of the validation algorithm.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm also avoids using any Monads, so it is verbose compared to a version that would use monads.

import Validator.Expr.Expr
import Validator.Expr.IfExpr

def dEnter (x: Expr) (res: List IfExpr := []): List IfExpr :=
  match x with
  | Expr.emptyset => res
  | Expr.epsilon => res
  | Expr.tree p y => (IfExpr.mk p y Expr.emptyset) :: res
  | Expr.or y z => dEnter y (dEnter z res)
  | Expr.concat y z =>
    if Expr.nullable y
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
    if Expr.nullable y
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

-- foldLoop is a more readable version of List.foldlM for imperative programmers:
def foldLoop (deriv: List Expr -> LTree -> Except String (List Expr)) (start: List Expr) (forest: List LTree): Except String (List Expr) := do
  let mut res := start
  for tree in forest do
    match deriv res tree with
    | Except.error err => throw err
    | Except.ok r => res := r
  return res

def deriv (xs: List Expr) (t: LTree): Except String (List Expr) :=
  if List.all xs Expr.unescapable
  then Except.ok xs
  else
    match t with
    | LTree.node label children =>
      let ifExprs: List IfExpr := List.flatten (List.map dEnter xs)
      -- des == derivatives of enter
      let des : List Expr := List.map (fun x => evalIfExpr x (Token.string label)) ifExprs
      -- dcs == derivatives of children, the ' is for the exception it is wrapped in
      -- see foldLoop for an explanation of what List.foldM does.
      let dcs' : Except String (List Expr) := List.foldlM deriv des children
      match dcs' with
      | Except.error err => Except.error err
      | Except.ok dcs =>
        -- dls == derivatives of leave, the ' is for the exception it is wrapped in
        let dls': Except String (List Expr) := dLeaves xs (List.map Expr.nullable dcs)
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
