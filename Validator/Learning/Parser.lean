-- Parser is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a Hedge.Node.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.

import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Regex.Compress
import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr
import Validator.Regex.Regex

import Validator.Parser.Hint
import Validator.Parser.Parser
import Validator.Parser.TokenTree

import Validator.Regex.Enter
import Validator.Regex.LeaveSmart

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserM

namespace Parser

def deriveEnter [DecidableEq φ] [ValidateM m (Hedge.Grammar.Symbol n φ) α]
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: Hedge.Grammar.Rules n φ l): m (Hedge.Grammar.Rules n φ (Regex.Symbol.nums xs)) := do
  let enters <- Regex.Enter.DeriveEnter.deriveEnter xs
  let token <- Parser.token
  return Hedge.Grammar.evalifs G Φ enters token

def deriveLeaveM [DecidableEq φ] [ValidateM m (Hedge.Grammar.Symbol n φ) α] (xs: Hedge.Grammar.Rules n φ l) (cs: Hedge.Grammar.Rules n φ (Regex.Symbol.nums xs)): m (Hedge.Grammar.Rules n φ l) :=
  Regex.Leave.DeriveLeaveM.deriveLeaveM xs (Vec.map cs Hedge.Grammar.Rule.null)

def deriveValue [DecidableEq φ] [ValidateM m (Hedge.Grammar.Symbol n φ) α]
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: Hedge.Grammar.Rules n φ l): m (Hedge.Grammar.Rules n φ l) := do
  deriveEnter G Φ xs >>= deriveLeaveM (α := α) xs

-- TODO: Is it possible to have a Parser type that can be proved to be of the correct shape, and have not expection throwing
-- for example: can you prove that your Parser will never return an Hint.leave after returning a Hint.field.
-- This class can be called the LawfulParser.
partial def derive [DecidableEq φ] [ValidateM m (Hedge.Grammar.Symbol n φ) α]
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: Hedge.Grammar.Rules n φ l): m (Hedge.Grammar.Rules n φ l) := do
  if List.all xs.toList Regex.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let childxs <- deriveEnter G Φ xs -- derive enter field
    let dchildxs <-
      match <- Parser.next with
      | Hint.value => deriveValue G Φ childxs -- derive child value
      | Hint.enter => derive G Φ childxs -- derive children, until return from a Hint.leave
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeaveM (α := α) xs dchildxs -- derive leave field
    derive G Φ xsLeave -- deriv next
  | Hint.value => deriveValue G Φ xs >>= derive G Φ -- derive value and then derive next
  | Hint.enter => derive G Φ xs >>= derive G Φ -- derive children, until return from a Hint.leave and then derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate {m} [DecidableEq φ] [ValidateM m (Hedge.Grammar.Symbol n φ) α]
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (x: Hedge.Grammar.Rule n φ): m Bool := do
  let dxs <- derive G Φ (Vec.cons x Vec.nil)
  return Hedge.Grammar.Rule.null dxs.head

def run [DecidableEq α] (G: Hedge.Grammar n (AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  TreeParserM.run' (validate G AnyEq.Pred.evalb G.start) t

-- Tests

open TokenTree (node)

#guard run
  (Hedge.Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Hedge.Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq (Token.string "d"), 1))
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptyset]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard run
  (Hedge.Grammar.mk (n := 4)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 3))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq (Token.string "d"), 1))
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        Regex.emptyset
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Hedge.Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard run
  (Hedge.Grammar.mk (n := 4)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 0))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq (Token.string "d"), 2))
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false
