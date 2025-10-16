import Validator.Expr.Pred

import Validator.Parser.Token
import Validator.Std.Hedge

-- CaptureExpr includes capturing groups
inductive CaptureExpr α where
  | emptyset
  | epsilon
  -- matched is extended to trees
  | matched (tok: α) (childExpr: CaptureExpr α)
  | tree (pred: Pred α) (childExpr: CaptureExpr α)
  | or (y z: CaptureExpr α)
  | concat (y z: CaptureExpr α)
  | star (y: CaptureExpr α)
  | group (id: Nat) (x: CaptureExpr α)
  deriving DecidableEq, Ord, Repr, Hashable

abbrev CaptureExprs α := List (CaptureExpr α)

instance [Ord α]: Ord (CaptureExpr α) := inferInstance

instance [Repr α]: Repr (CaptureExpr α) := inferInstance

instance [DecidableEq α]: DecidableEq (CaptureExpr α) := inferInstance

instance [DecidableEq α]: BEq (CaptureExpr α) := inferInstance

instance [Hashable α]: Hashable (CaptureExpr α) := inferInstance

def CaptureExpr.nullable (x: CaptureExpr α): Bool :=
  match x with
  | CaptureExpr.emptyset => false
  | CaptureExpr.epsilon => true
  -- matched is technically the same as epsilon, except that it stores the matched token and childExpr.
  | CaptureExpr.matched _ _ => true
  | CaptureExpr.tree _ _ => false
  | CaptureExpr.or y z => nullable y || nullable z
  | CaptureExpr.concat y z => nullable y && nullable z
  | CaptureExpr.star _ => true
  | CaptureExpr.group _ y => nullable y

def CaptureExpr.unescapable (x: CaptureExpr α): Bool :=
  match x with
  | CaptureExpr.emptyset => true
  | _ => false

-- smartOr is a smart constructor for the or operator.
def CaptureExpr.smartOr (x y: CaptureExpr α): CaptureExpr α :=
  match x with
  | CaptureExpr.emptyset => y
  | _ =>
    match y with
    | CaptureExpr.emptyset => x
    | _ => CaptureExpr.or x y

-- smartConcat is a smart constructor for the concat operator.
def CaptureExpr.smartConcat (x y: CaptureExpr α): CaptureExpr α :=
  match x with
  | CaptureExpr.emptyset => CaptureExpr.emptyset
  | CaptureExpr.epsilon => y
  | _ =>
    match y with
    | CaptureExpr.emptyset => CaptureExpr.emptyset
    | CaptureExpr.epsilon => x
    | _ => CaptureExpr.concat x y

-- smartStar is a smart constructor for the star operator.
def CaptureExpr.smartStar (x: CaptureExpr α): CaptureExpr α :=
  match x with
  | CaptureExpr.star _ => x
  | CaptureExpr.emptyset => CaptureExpr.epsilon
  | _ => CaptureExpr.star x

def CaptureExpr.smartGroup (id: Nat) (x: CaptureExpr α): CaptureExpr α :=
  match x with
  | CaptureExpr.emptyset => CaptureExpr.emptyset
  | _ => CaptureExpr.group id x

-- neutralize replaces all tree operators with emptyset.
-- It is used when deriving concat.
-- This way we do not lose capture information on nullable expressions.
def CaptureExpr.neutralize (x: CaptureExpr α): CaptureExpr α :=
  match x with
  | CaptureExpr.emptyset => CaptureExpr.emptyset
  | CaptureExpr.epsilon => CaptureExpr.epsilon
  -- matched is handled exactly the same as epsilon, by simply preserving itself and the matched tok and childExpr.
  | CaptureExpr.matched tok childExpr => CaptureExpr.matched tok (neutralize childExpr)
  | CaptureExpr.tree _ _ => CaptureExpr.emptyset
  | CaptureExpr.or y z => CaptureExpr.smartOr (neutralize y) (neutralize z)
  | CaptureExpr.concat y z => CaptureExpr.smartConcat (neutralize y) (neutralize z)
  | CaptureExpr.star y => CaptureExpr.smartStar (neutralize y)
  | CaptureExpr.group id y => CaptureExpr.smartGroup id (neutralize y)
