import Validator.Std.Vec

import Validator.Expr.Regex
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Symbol

namespace Enter

def deriveEnter (xs: Rules n (Pred α) l): IfExprs n α (Symbol.nums xs) :=
  Vec.map
    (Symbol.extractsFrom xs).2
    (fun (pred, ref) => IfExpr.mk pred ref)

class DeriveEnter (m: Type -> Type u) (n: Nat) (α: outParam Type) where
  deriveEnter {l: Nat} (xs: Rules n (Pred α) l): m (IfExprs n α (Symbol.nums xs))
