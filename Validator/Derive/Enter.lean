import Mathlib.Data.Vector.Snoc

import Validator.Expr.Regex
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Symbol

namespace Enter

def deriveEnter (xs: Rules μ α Pred ν): IfExprs μ α (Symbol.nums xs) :=
  List.Vector.map
    (fun (pred, ref) => IfExpr.mk pred ref)
    (Symbol.Symbols.cast
      (Symbol.extracts xs List.Vector.nil).2
      (by ac_rfl)
    )

class DeriveEnter (m: Type -> Type u) (μ: Nat) (α: outParam Type) where
  deriveEnter {ν: Nat} (xs: Rules μ α Pred ν): m (IfExprs μ α (Symbol.nums xs))

def deriveEnter_list (xs: List (Rule μ α Pred)): List (IfExpr μ α) :=
  List.map (fun (pred, ref) => IfExpr.mk pred ref) (Symbol.extracts_list xs []).2
