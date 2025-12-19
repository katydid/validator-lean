import Std

import Validator.Std.Vec

import Validator.Regex.Regex

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
abbrev Rule (n: Nat) (α: Type) (φ: (α: Type) -> Type) := φ α × Regex (Ref n)
abbrev Rules (n: Nat) (α: Type) (φ: (α: Type) -> Type) := { xs: List (Rule n α φ) // xs.length > 0 }

structure RTG (n: Nat) (α: Type) (φ: (α: Type) -> Type) where
  start: { s: List (Ref n) // s.length > 0 }
  prods: Vec (Rules n α φ) n

def RTG.lookup (n: Nat) (α: Type) (φ: (α: Type) -> Type)
  (g: RTG n α φ) (ref: Fin n): Rules n α φ :=
  Vec.get g.prods ref
