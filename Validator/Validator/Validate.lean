-- ParserConciseCompress is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a Hedge.Node.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- It does add compression for a small optimization, see lines marked with NEW

import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Hedge.Compress
import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr
import Validator.Regex.Regex

import Validator.Derive.Enter
import Validator.Derive.Leave

import Validator.Parser.TokenTree
import Validator.Parser.Parser
import Validator.Parser.Hint

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemM

namespace Validate

def deriveEnter [DecidableEq φ] [ValidateM m n φ α]
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: Rules n φ l): m (Rules n φ (Symbol.nums xs)) := do
  let token <- Parser.token
  let enters <- Enter.DeriveEnter.deriveEnter xs
  return IfExpr.evals G Φ enters token

def deriveLeaveM [ValidateM m n φ α] (xs: Rules n φ l) (cs: Rules n φ (Symbol.nums xs)): m (Rules n φ l) :=
  Leave.DeriveLeaveM.deriveLeaveM xs (Vec.map cs Rule.nullable)

def deriveValue [DecidableEq φ] [ValidateM m n φ α]
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: Rules n φ l): m (Rules n φ l) := do
  deriveLeaveM (α := α) xs (<- deriveEnter G Φ xs)

partial def derive [DecidableEq φ] [ValidateM m n φ α]
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: Rules n φ l): m (Rules n φ l) := do
  if List.all xs.toList Regex.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let childxs <- deriveEnter G Φ xs -- derive enter field
    let dchildxs <-
      match <- Parser.next with
      | Hint.value => deriveValue G Φ childxs -- derive child value
      | Hint.enter =>
        let ⟨_, cchildxs, indices⟩ <- Compress.compressM childxs -- NEW: compress
        let cdchildxs <- derive G Φ cchildxs -- derive children, until return from a Hint.leave
        Compress.expandM indices cdchildxs -- NEW: expand
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeaveM (α := α) xs dchildxs -- derive leave field
    derive G Φ xsLeave -- deriv next
  | Hint.value => deriveValue G Φ xs >>= derive G Φ -- derive value and then derive next
  | Hint.enter =>
    let ⟨_, cchildxs, indices⟩ <- Compress.compressM xs -- NEW: compress
    let cdchildxs <- derive G Φ cchildxs -- derive children, until return from a Hint.leave
    let dchildxs <- Compress.expandM indices cdchildxs -- NEW: expand
    derive G Φ dchildxs -- derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate {m} {n: Nat} {α: Type} [DecidableEq φ]
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  [ValidateM m n φ α] (x: Rule n φ): m Bool := do
  let dxs <- derive G Φ (Vec.cons x Vec.nil)
  return Rule.nullable dxs.head

def run {α: Type} [DecidableEq α] [Hashable α] (G: Grammar n (Pred α)) (t: Hedge.Node α): Except String Bool :=
  TreeParserMemM.run' (n := n) (φ := Pred α) (validate G Pred.evalb G.start) t

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Grammar.mk (n := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.eq (Token.string "d"), 1))
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptyset]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard run
  (Grammar.mk (n := 4)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 3))
        (Regex.symbol (Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.eq (Token.string "d"), 1))
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        Regex.emptyset
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard run
  (Grammar.mk (n := 4)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 0))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.eq (Token.string "d"), 2))
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false
