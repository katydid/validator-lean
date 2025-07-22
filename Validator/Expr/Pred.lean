import Validator.Parser.Token

-- TODO: consider a more flexible Predicate model, for example:
-- https://github.com/katydid/regex-deriv-lean/blob/main/RegexDeriv/Regex/Predicate.lean
-- First do upgrade the regex-deriv-lean to lean 4.21 and update definitions to LawfulOrd

inductive Pred where
  | eq (t: Token)
  deriving DecidableEq, Ord, Repr, Hashable

namespace Pred

def eval (p: Pred) (t: Token): Bool :=
  match p with
  | eq t' => t == t'

def eqStr (s: String): Pred :=
  Pred.eq (Token.string s)
