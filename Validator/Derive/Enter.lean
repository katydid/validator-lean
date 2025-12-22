import Validator.Std.Vec

import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.Symbol
import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr

namespace Enter

def deriveEnter (xs: Rules n φ l): IfExprs n φ (Symbol.nums xs) :=
  (Symbol.extractsFrom xs).2

class DeriveEnter (m: Type -> Type u) (n: Nat) (φ: Type) where
  deriveEnter {l: Nat} (xs: Rules n φ l): m (IfExprs n φ (Symbol.nums xs))
