import Mathlib.Data.Vector.Snoc

import Validator.Expr.Regex
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Symbol

namespace Enter

def deriveEnter (xs: Rules n α Pred l): IfExprs n α (Symbol.nums xs) :=
  List.Vector.map
    (fun (pred, ref) => IfExpr.mk pred ref)
    (Symbol.Symbols.cast
      (Symbol.extracts xs List.Vector.nil).2
      (by ac_rfl)
    )

class DeriveEnter (m: Type -> Type u) (n: Nat) (α: outParam Type) where
  deriveEnter {l: Nat} (xs: Rules n α Pred l): m (IfExprs n α (Symbol.nums xs))

def deriveEnter_list (xs: List (Rule n α Pred)): List (IfExpr n α) :=
  List.map (fun (pred, ref) => IfExpr.mk pred ref) (Symbol.extracts_list xs []).2
