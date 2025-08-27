import Validator.Expr.Pred

inductive Expr α where
  | emptyset
  | epsilon
  | tree (labelPred: Pred α) (childrenExpr: Expr α)
  | or (y z: Expr α)
  | concat (y z: Expr α)
  | star (y: Expr α)
  deriving DecidableEq, Ord, Repr, Hashable

abbrev Exprs α := List (Expr α)

instance [Ord α]: Ord (Expr α) := inferInstance

instance [Repr α]: Repr (Expr α) := inferInstance

instance [DecidableEq α]: DecidableEq (Expr α) := inferInstance

instance [DecidableEq α]: BEq (Expr α) := inferInstance

instance [Hashable α]: Hashable (Expr α) := inferInstance

def Expr.nullable (x: Expr α): Bool :=
  match x with
  | Expr.emptyset => false
  | Expr.epsilon => true
  | Expr.tree _ _ => false
  | Expr.or y z => nullable y || nullable z
  | Expr.concat y z => nullable y && nullable z
  | Expr.star _ => true

def Expr.unescapable (x: Expr α): Bool :=
  match x with
  | Expr.emptyset => true
  | _ => false

namespace Expr

def onlyif (cond: Prop) [dcond: Decidable cond] (x: Expr α): Expr α :=
  if cond then x else Expr.emptyset

def smartOr (x y: Expr α): Expr α :=
  match x with
  | Expr.emptyset => y
  | _ =>
    match y with
    | Expr.emptyset => x
    | _ => Expr.or x y

def smartConcat (x y: Expr α): Expr α :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => y
  | _ =>
    match y with
    | Expr.emptyset => Expr.emptyset
    | Expr.epsilon => x
    | _ => Expr.concat x y

def smartStar (x: Expr α): Expr α :=
  match x with
  | Expr.star _ => x
  | Expr.emptyset => Expr.epsilon
  | _ => Expr.star x
