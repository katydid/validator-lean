import Validator.Std.Vec

import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Regex

namespace Enter

def deriveEnter (xs: Vec (Regex σ) l): Vec σ (Symbol.nums xs) :=
  (Symbol.extractsFrom xs).2

class DeriveEnter (m: Type -> Type u) (σ: Type) where
  deriveEnter {l: Nat} (xs: Vec (Regex σ) l): m (Vec σ (Symbol.nums xs))
