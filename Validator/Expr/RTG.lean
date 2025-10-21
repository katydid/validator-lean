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

abbrev Ref μ := Fin μ
abbrev Rule (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) := Φ α × Regex (Ref μ)
abbrev Rules (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) := { xs: List (Rule μ α Φ) // xs.length > 0 }

structure RTG (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) where
  start: { s: List (Ref μ) // s.length > 0 }
  prods: Vector (Rules μ α Φ) μ

def RTG.lookup (μ: Nat) (α: Type) (Φ: (α: Type) -> Type)
  (g: RTG μ α Φ) (ref: Fin μ): Rules μ α Φ :=
  Vector.get g.prods ref
