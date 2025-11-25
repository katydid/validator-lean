import Std

import Validator.Expr.Regex

namespace RegularTreeGrammar

-- Definition of a RegularTreeGrammar
-- G = (N, T, S, P)
-- N = a finite set of non-terminals
-- T = a finite set of terminals
-- S = a set of start non-terminals
-- P = a set of production rules of the form X -> a(r)
-- where
--   a ∈ T
--   r is a regular expression over N

abbrev Ref n := Fin n
abbrev Rule (n: Nat) (α: Type) (Φ: (α: Type) -> Type) := Φ α × Regex (Ref n)
abbrev Rules (n: Nat) (α: Type) (Φ: (α: Type) -> Type) := { xs: List (Rule n α Φ) // xs.length > 0 }

structure RTG (n: Nat) (α: Type) (Φ: (α: Type) -> Type) where
  start: { s: List (Ref n) // s.length > 0 }
  prods: Vector (Rules n α Φ) n

def RTG.lookup (n: Nat) (α: Type) (Φ: (α: Type) -> Type)
  (g: RTG n α Φ) (ref: Fin n): Rules n α Φ :=
  Vector.get g.prods ref
