import Validator.Expr.Expr
import Validator.Expr.IfExpr

namespace Enter

def enter (x: Expr μ α) (res: IfExprs μ α := []): IfExprs μ α :=
  match x with
  | Expr.emptyset => res
  | Expr.epsilon => res
  | Expr.tree pred childRef => (IfExpr.mk pred childRef) :: res
  | Expr.or y z => enter y (enter z res)
  | Expr.concat y z =>
    if Expr.nullable y
    then enter y (enter z res)
    else enter y res
  | Expr.star y => enter y res

def deriveEnter (xs: Exprs μ α): IfExprs μ α :=
  List.flatten (List.map Enter.enter xs)

theorem deriveEnter_nil_is_nil {α: Type} {μ: Nat}:
  @deriveEnter μ α [] = [] := by
  unfold deriveEnter
  simp

theorem deriveEnter_cons_is_concat {α: Type} (x: Expr μ α) (xs: Exprs μ α):
  deriveEnter (x::xs) = (deriveEnter [x]) ++ (deriveEnter xs) := by
  unfold deriveEnter
  simp

class DeriveEnter (m: Type -> Type u) (μ: Nat) (α: outParam Type)  where
  deriveEnter (xs: Exprs μ α): m (IfExprs μ α)
