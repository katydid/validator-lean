import Validator.Capturer.CaptureExpr
import Validator.Capturer.CaptureIfExpr

namespace CaptureEnter

def enter (x: CaptureExpr α) (res: CaptureIfExprs α := []): CaptureIfExprs α :=
  match x with
  | CaptureExpr.emptyset => res
  | CaptureExpr.epsilon => res
  -- matched should behave just like epsilon
  | CaptureExpr.matched _ _ => res
  | CaptureExpr.tree pred childrenExpr => (CaptureIfExpr.mk pred childrenExpr CaptureExpr.emptyset) :: res
  | CaptureExpr.or y z => enter y (enter z res)
  | CaptureExpr.concat y z =>
    if CaptureExpr.nullable y
    then enter y (enter z res)
    else enter y res
  | CaptureExpr.star y => enter y res
  -- The group is not relevant at this point, are only extracting if expressions.
  | CaptureExpr.group _id y => enter y res

def deriveEnter (xs: CaptureExprs α): CaptureIfExprs α :=
  List.flatten (List.map CaptureEnter.enter xs)

class DeriveEnter (m: Type -> Type u) where
  deriveEnter (xs: CaptureExprs α): m (CaptureIfExprs α)
