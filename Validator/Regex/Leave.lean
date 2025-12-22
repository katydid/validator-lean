import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Point
import Validator.Regex.Regex
import Validator.Regex.Replace

namespace Leave

def deriveLeaves
  (rs: Vec (Regex σ) l)
  (ps: Vec Bool (Symbol.nums rs))
  : (Vec (Regex σ) l) :=
  let replaces: Vec (σ × Bool) (Symbol.nums rs) := Vec.zip (Symbol.extractsFrom rs).2 ps
  let replaced: Vec (Regex (σ × Bool)) l := Symbol.replacesFrom (Symbol.extractsFrom rs).1 replaces
  Regex.Point.derives replaced

def deriveLeaveM [Monad m] {l: Nat} (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l) := do
  return deriveLeaves xs ns

class DeriveLeaveM (m: Type -> Type u) (σ: Type) where
  deriveLeaveM {l: Nat} (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l)
