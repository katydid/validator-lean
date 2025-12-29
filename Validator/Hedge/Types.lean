import Validator.Regex.Regex

-- ## Definition 3.2.3: Regular Hedge Grammar
--   𝐺 = (𝑁, 𝑇, 𝑆, 𝑃)
--   𝑁 a finite set of non-terminals
--   𝑇 a finite set of terminals
--   𝑆 the start symbol of a regular hedge grammar is a regular expression comprising pairs of nonterminals and terminals (a regular expression over N × T)
--   𝑃 a set of production rules of a regular hedge grammar are of the form X → r such that r is a regular expression over N × T.

namespace Hedge

-- Ref is a non-terminal, where n represents the number of non-terminals
abbrev Grammar.Ref (n: Nat) := Fin n

abbrev Grammar.Symbol (n: Nat) (φ: Type) := (φ × Ref n)

abbrev Grammar.Rule (n: Nat) (φ: Type) := Regex (Symbol n φ)

structure Grammar (n: Nat) (φ: Type) where
  start: Grammar.Rule n φ
  prods: Vec (Grammar.Rule n φ) n

end Hedge

namespace Hedge.Grammar

abbrev Rules (n: Nat) (φ: Type) (l: Nat) := Vec (Rule n φ) l

abbrev Symbols n φ l := Vec (Symbol n φ) l

def hashVector [Hashable α] (xs: Vec α n): UInt64 :=
  hash xs.toList

instance (α: Type) (n: Nat) [Hashable α] : Hashable (Vec α n) where
  hash := hashVector

def hashRules {n: Nat} {φ: Type} {l: Nat} [Hashable φ] (xs: Rules n φ l): UInt64 :=
  hash xs.toList

instance (n: Nat) (φ: Type) (l: Nat) [Hashable φ] : Hashable (Rules n φ l) where
  hash := hashRules
