import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Regex.Smart
import Validator.Regex.Num
import Validator.Regex.Extract
import Validator.Regex.Leave

namespace Regex.LeaveSmart

-- leaves takes a vector of expressions and vector of bools.
-- The vectors of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each symbol expression with either an emptystr or emptyset.
def leaves
  (xs: Vec (Regex σ) l)
  (ns: Vec Bool (Symbol.nums xs))
  : (Vec (Regex σ) l) :=
  let (regexes, symbols) := Symbol.extractsFrom xs
  let res: Vec (σ × Bool) (Symbol.nums xs) := Vec.zip symbols ns
  let res': Vec (Regex (σ × Bool)) l := Symbol.replacesFrom regexes res
  Regex.Smart.derive_points res'

def deriveLeaveM [Monad m] {l: Nat} (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l) := do
  return leaves xs ns
