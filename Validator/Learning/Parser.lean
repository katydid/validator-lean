-- Parser is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a Hedge.Node.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.

import Validator.Expr.Compress
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex

import Validator.Parser.Hint
import Validator.Parser.Parser
import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Derive.Enter
import Validator.Derive.Leave

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserM

namespace Parser

def deriveEnter [DecidableEq α] [ValidateM m μ α] (g: Grammar μ α Pred) (xs: Rules μ α Pred ν): m (Rules μ α Pred (Symbol.nums xs)) := do
  let enters <- Enter.DeriveEnter.deriveEnter xs
  let token <- Parser.token
  return IfExpr.evals g enters token

def deriveLeaveM [DecidableEq α] [ValidateM m μ α] (xs: Rules μ α Pred ν) (cs: Rules μ α Pred (Symbol.nums xs)): m (Rules μ α Pred ν) :=
  Leave.DeriveLeaveM.deriveLeaveM xs (List.Vector.map Rule.nullable cs)

def deriveValue [DecidableEq α] [ValidateM m μ α] (g: Grammar μ α Pred) (xs: Rules μ α Pred ν): m (Rules μ α Pred ν) := do
  deriveEnter g xs >>= deriveLeaveM xs

-- TODO: Is it possible to have a Parser type that can be proved to be of the correct shape, and have not expection throwing
-- for example: can you prove that your Parser will never return an Hint.leave after returning a Hint.field.
-- This class can be called the LawfulParser.
partial def derive [DecidableEq α] [ValidateM m μ α] (g: Grammar μ α Pred) (xs: Rules μ α Pred ν): m (Rules μ α Pred ν) := do
  if List.all xs.toList Regex.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let childxs <- deriveEnter g xs -- derive enter field
    let dchildxs <-
      match <- Parser.next with
      | Hint.value => deriveValue g childxs -- derive child value
      | Hint.enter => derive g childxs -- derive children, until return from a Hint.leave
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeaveM xs dchildxs -- derive leave field
    derive g xsLeave -- deriv next
  | Hint.value => deriveValue g xs >>= derive g -- derive value and then derive next
  | Hint.enter => derive g xs >>= derive g -- derive children, until return from a Hint.leave and then derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate {m} [DecidableEq α] [ValidateM m μ α] (g: Grammar μ α Pred) (x: Rule μ α Pred): m Bool := do
  let dxs <- derive g (List.Vector.cons x List.Vector.nil)
  return Rule.nullable dxs.head

def run [DecidableEq α] (g: Grammar μ α Pred) (t: Hedge.Node α): Except String Bool :=
  TreeParserM.run' (validate g g.start) t

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
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
  (Grammar.mk (μ := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
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
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptyset]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard run
  (Grammar.mk (μ := 4)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
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
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
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
  (Grammar.mk (μ := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
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
  (Grammar.mk (μ := 4)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
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
