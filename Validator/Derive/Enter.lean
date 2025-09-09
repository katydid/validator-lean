import Validator.Std.Linter.DetectClassical

import Validator.Expr.Expr
import Validator.Expr.IfExpr

namespace Enter

def enter (x: Expr α) (res: IfExprs α := []): IfExprs α :=
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

def deriveEnter (xs: Exprs α): IfExprs α :=
  List.flatten (List.map Enter.enter xs)

theorem deriveEnter_nil_is_nil {α: Type u}:
  @deriveEnter α [] = [] := by
  unfold deriveEnter
  simp

theorem deriveEnter_cons_is_concat {α: Type u} (x: Expr α) (xs: Exprs α):
  deriveEnter (x::xs) = (deriveEnter [x]) ++ (deriveEnter xs) := by
  unfold deriveEnter
  simp

class DeriveEnter (m: Type -> Type u) (α: outParam Type)  where
  deriveEnter (xs: Exprs α): m (IfExprs α)
