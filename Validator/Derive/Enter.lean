import Validator.Std.Vec

import Validator.Expr.Regex
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Symbol

namespace Enter

def deriveEnter (xs: Rules n (Pred α) l): IfExprs n α (Symbol.nums xs) :=
  List.Vector.map
    (fun (pred, ref) => IfExpr.mk pred ref)
    (Symbol.Symbols.cast
      (Symbol.extracts xs List.Vector.nil).2
      (by ac_rfl)
    )

class DeriveEnter (m: Type -> Type u) (n: Nat) (α: outParam Type) where
  deriveEnter {l: Nat} (xs: Rules n (Pred α) l): m (IfExprs n α (Symbol.nums xs))
