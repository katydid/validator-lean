import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Point
import Validator.Regex.Regex
import Validator.Regex.Replace

namespace Leave

def leave
  (r: Regex σ)
  (ps: Vec Bool (Symbol.num r))
  : Regex σ :=
  let replaces: Vec (σ × Bool) (Symbol.num r) := Vec.zip (Symbol.extractFrom r).2 ps
  let replaced: Regex (σ × Bool) := Symbol.replaceFrom (Symbol.extractFrom r).1 replaces
  Regex.Point.derive replaced

-- leaves takes a vector of expressions and vector of bools.
-- The vectors of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each symbol expression with either an emptystr or emptyset.
def leaves
  (rs: Vec (Regex σ) l)
  (ps: Vec Bool (Symbol.nums rs))
  : (Vec (Regex σ) l) :=
  let replaces: Vec (σ × Bool) (Symbol.nums rs) := Vec.zip (Symbol.extractsFrom rs).2 ps
  let replaced: Vec (Regex (σ × Bool)) l := Symbol.replacesFrom (Symbol.extractsFrom rs).1 replaces
  Regex.Point.derives replaced

def deriveLeaveM [Monad m] {l: Nat} (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l) := do
  return leaves xs ns

class DeriveLeaveM (m: Type -> Type u) (σ: Type) where
  deriveLeaveM {l: Nat} (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l)
