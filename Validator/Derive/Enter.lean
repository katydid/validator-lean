import Validator.Expr.Expr
import Validator.Expr.IfExpr

namespace Enter

def enter (x: Expr) (res: List IfExpr := []): List IfExpr :=
  match x with
  | Expr.emptyset => res
  | Expr.epsilon => res
  | Expr.tree pred childrenExpr => (IfExpr.mk pred childrenExpr Expr.emptyset) :: res
  | Expr.or y z => enter y (enter z res)
  | Expr.concat y z =>
    if Expr.nullable y
    then enter y (enter z res)
    else enter y res
  | Expr.star y => enter y res

def deriveEnter (xs: List Expr): List IfExpr :=
  List.flatten (List.map Enter.enter xs)

class DeriveEnter (m: Type -> Type u) where
  deriveEnter (xs: List Expr): m (List IfExpr)
