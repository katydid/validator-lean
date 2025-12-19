import Validator.Std.Vec

import Validator.Hedge.Grammar
import Validator.Regex.Regex
import Validator.Regex.Smart
import Validator.Regex.Symbol
import Validator.Derive.Enter

namespace Leave

-- deriveLeaves takes a vector of expressions and vector of bools.
-- The vectors of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each symbol expression with either an emptystr or emptyset.
def deriveLeaves
  (xs: Rules n φ l)
  (ns: Vec Bool (Symbol.nums xs))
  : (Rules n φ l) :=
  let (regexes, symbols) := Symbol.extractsFrom xs
  let res: Vec ((φ × Ref n) × Bool) (Symbol.nums xs) := Vec.zip symbols ns
  let res': Vec (Regex ((φ × Ref n) × Bool)) l := Symbol.replacesFrom regexes res
  Regex.Smart.derive_pairs res'

def deriveLeaveM [Monad m] {n: Nat} {l: Nat} (xs: Rules n φ l) (ns: Vec Bool (Symbol.nums xs)): m (Rules n φ l) := do
  return deriveLeaves xs ns

class DeriveLeaveM (m: Type -> Type u) (n: Nat) (φ: Type) where
  deriveLeaveM {l: Nat} (xs: Rules n φ l) (ns: Vec Bool (Symbol.nums xs)): m (Rules n φ l)
