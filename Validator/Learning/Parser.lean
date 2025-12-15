-- Parser is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a Hedge.Node.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.

import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Expr.Compress
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex

import Validator.Parser.Hint
import Validator.Parser.Parser
import Validator.Parser.TokenTree

import Validator.Derive.Enter
import Validator.Derive.Leave

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserM

namespace Parser

def deriveEnter [DecidableEq φ] [ValidateM m n φ α]
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (xs: Rules n φ l): m (Rules n φ (Symbol.nums xs)) := do
  let enters <- Enter.DeriveEnter.deriveEnter xs
  let token <- Parser.token
  return IfExpr.evals g Φ enters token

def deriveLeaveM [DecidableEq φ] [ValidateM m n φ α] (xs: Rules n φ l) (cs: Rules n φ (Symbol.nums xs)): m (Rules n φ l) :=
  Leave.DeriveLeaveM.deriveLeaveM xs (Vec.map cs Rule.nullable)

def deriveValue [DecidableEq φ] [ValidateM m n φ α]
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (xs: Rules n φ l): m (Rules n φ l) := do
  deriveEnter g Φ xs >>= deriveLeaveM (α := α) xs

-- TODO: Is it possible to have a Parser type that can be proved to be of the correct shape, and have not expection throwing
-- for example: can you prove that your Parser will never return an Hint.leave after returning a Hint.field.
-- This class can be called the LawfulParser.
partial def derive [DecidableEq φ] [ValidateM m n φ α]
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (xs: Rules n φ l): m (Rules n φ l) := do
  if List.all xs.toList Regex.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let childxs <- deriveEnter g Φ xs -- derive enter field
    let dchildxs <-
      match <- Parser.next with
      | Hint.value => deriveValue g Φ childxs -- derive child value
      | Hint.enter => derive g Φ childxs -- derive children, until return from a Hint.leave
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeaveM (α := α) xs dchildxs -- derive leave field
    derive g Φ xsLeave -- deriv next
  | Hint.value => deriveValue g Φ xs >>= derive g Φ -- derive value and then derive next
  | Hint.enter => derive g Φ xs >>= derive g Φ -- derive children, until return from a Hint.leave and then derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate {m} [DecidableEq φ] [ValidateM m n φ α]
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (x: Rule n φ): m Bool := do
  let dxs <- derive g Φ (Vec.cons x Vec.nil)
  return Rule.nullable dxs.head

def run [DecidableEq α] (g: Grammar n (Pred α)) (t: Hedge.Node α): Except String Bool :=
  TreeParserM.run' (validate g Pred.eval g.start) t

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
