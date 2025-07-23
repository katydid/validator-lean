import Validator.Parser.Token

-- TODO: consider a more flexible Predicate model, for example:
-- https://github.com/katydid/regex-deriv-lean/blob/main/RegexDeriv/Regex/Predicate.lean
-- First do upgrade the regex-deriv-lean to lean 4.21 and update definitions to LawfulOrd

inductive Pred (α: Type) where
  | eq (t: α)
  deriving DecidableEq, Ord, Repr, Hashable

instance [Ord α]: Ord (Pred α) := inferInstance

instance [Repr α]: Repr (Pred α) := inferInstance

instance [DecidableEq α]: DecidableEq (Pred α) := inferInstance

instance [DecidableEq α]: BEq (Pred α) := inferInstance

instance [Hashable α]: Hashable (Pred α) := inferInstance

namespace Pred

def eval [BEq α] (p: Pred α) (t: α): Bool :=
  match p with
  | eq t' => t == t'
