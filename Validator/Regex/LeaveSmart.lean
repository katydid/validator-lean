import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Regex.Smart
import Validator.Regex.Symbol

namespace LeaveSmart

-- deriveLeaves takes a vector of expressions and vector of bools.
-- The vectors of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each symbol expression with either an emptystr or emptyset.
def deriveLeaves
  (xs: Vec (Regex σ) l)
  (ns: Vec Bool (Symbol.nums xs))
  : (Vec (Regex σ) l) :=
  let (regexes, symbols) := Symbol.extractsFrom xs
  let res: Vec (σ × Bool) (Symbol.nums xs) := Vec.zip symbols ns
  let res': Vec (Regex (σ × Bool)) l := Symbol.replacesFrom regexes res
  Regex.Smart.derive_points res'

def deriveLeaveM [Monad m] {l: Nat} (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l) := do
  return deriveLeaves xs ns

class DeriveLeaveM (m: Type -> Type u) (σ: Type) where
  deriveLeaveM {l: Nat} (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l)
