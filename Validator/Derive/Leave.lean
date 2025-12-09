import Validator.Std.Vec

import Validator.Expr.Grammar
import Validator.Expr.Regex
import Validator.Expr.Symbol
import Validator.Derive.Enter

namespace Leave

-- deriveLeaves takes a vector of expressions and vector of bools.
-- The vectors of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each symbol expression with either an emptystr or emptyset.
def deriveLeaves
  (xs: Rules n (Pred α) l)
  (ns: Vec Bool (Symbol.nums xs))
  : (Rules n (Pred α) l) :=
  let (regexes, symbols) := Symbol.extractsFrom xs
  let res: Vec ((Pred α × Ref n) × Bool) (Symbol.nums xs) := Vec.zip symbols ns
  let res': Vec (Regex ((Pred α × Ref n) × Bool)) l := Symbol.replacesFrom regexes res
  Regex.smartDerives2 res'

def deriveLeaveM [Monad m] {n: Nat} {l: Nat} (xs: Rules n (Pred α) l) (ns: Vec Bool (Symbol.nums xs)): m (Rules n (Pred α) l) := do
  return deriveLeaves xs ns

class DeriveLeaveM (m: Type -> Type u) (n: Nat) (α: outParam Type) where
  deriveLeaveM {l: Nat} (xs: Rules n (Pred α) l) (ns: Vec Bool (Symbol.nums xs)): m (Rules n (Pred α) l)
