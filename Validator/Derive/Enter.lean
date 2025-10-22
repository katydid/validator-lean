import Validator.Expr.Regex
import Validator.Expr.Grammar
import Validator.Expr.IfExpr

namespace Enter

def enter (x: Rule μ α Pred) (res: IfExprs μ α := []): IfExprs μ α :=
  match x with
  | Regex.emptyset => res
  | Regex.emptystr => res
  | Regex.symbol (pred, childRef) => (IfExpr.mk pred childRef) :: res
  | Regex.or y z => enter y (enter z res)
  | Regex.concat y z =>
    if Regex.nullable y
    then enter y (enter z res)
    else enter y res
  | Regex.star y => enter y res

def deriveEnter (xs: Rules μ α Pred): IfExprs μ α :=
  List.flatten (List.map Enter.enter xs)

theorem deriveEnter_nil_is_nil {α: Type} {μ: Nat}:
  @deriveEnter μ α [] = [] := by
  unfold deriveEnter
  simp

theorem deriveEnter_cons_is_concat {α: Type} (x: Rule μ α Pred) (xs: Rules μ α Pred):
  deriveEnter (x::xs) = (deriveEnter [x]) ++ (deriveEnter xs) := by
  unfold deriveEnter
  simp

class DeriveEnter (m: Type -> Type u) (μ: Nat) (α: outParam Type)  where
  deriveEnter (xs: Rules μ α Pred): m (IfExprs μ α)
