-- Parser is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a ParseTree.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Parser.Hint
import Validator.Parser.Parser
import Validator.Std.ParseTree
import Validator.Parser.TokenTree

import Validator.Derive.Enter
import Validator.Derive.Leave

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserM

namespace Parser

def deriveEnter [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (xs: Exprs μ α): m (Exprs μ α) := do
  let enters <- Enter.DeriveEnter.deriveEnter xs
  let token <- Parser.token
  return IfExpr.evals g enters token

def deriveLeaveM [DecidableEq α] [ValidateM m μ α] (xs: Exprs μ α) (cs: Exprs μ α): m (Exprs μ α) :=
  Leave.DeriveLeaveM.deriveLeaveM xs (List.map Expr.nullable cs)

def deriveValue [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (xs: Exprs μ α): m (Exprs μ α) := do
  deriveEnter g xs >>= deriveLeaveM xs

-- TODO: Is it possible to have a Parser type that can be proved to be of the correct shape, and have not expection throwing
-- for example: can you prove that your Parser will never return an Hint.leave after returning a Hint.field.
-- This class can be called the LawfulParser.
partial def derive [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (xs: Exprs μ α): m (Exprs μ α) := do
  if List.all xs Expr.unescapable then
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

def validate {m} [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (x: Expr μ α): m Bool := do
  let dxs <- derive g [x]
  match dxs with
  | [dx] => return Expr.nullable dx
  | _ => throw "expected one expression"

def run [DecidableEq α] (g: Expr.Grammar μ α) (t: ParseTree α): Except String Bool :=
  TreeParserM.run' (validate g g.lookup0) t

-- Tests

open TokenTree (node)

#guard run
  (Expr.Grammar.singleton Expr.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.tree (Pred.eq (Token.string "b")) 2)
      , Expr.epsilon
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b")) 2)
        (Expr.tree (Pred.eq (Token.string "c")) 2)
      )
      , Expr.epsilon
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 4)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b")) 2)
        (Expr.tree (Pred.eq (Token.string "c")) 3)
      )
      , Expr.epsilon
      , (Expr.tree (Pred.eq (Token.string "d")) 2)
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.emptyset]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 5)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b")) 4)
        (Expr.tree (Pred.eq (Token.string "c")) 3)
      )
      , Expr.epsilon
      , (Expr.tree (Pred.eq (Token.string "d")) 2)
      , Expr.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b"))
          2
        )
        Expr.emptyset
      )
      , Expr.epsilon
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 4)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b"))
          2
        )
        (Expr.tree (Pred.eq (Token.string "c"))
          3
        )
      )
      , Expr.epsilon
      , Expr.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 5)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b"))
          1
        )
        (Expr.tree (Pred.eq (Token.string "c"))
          2
        )
      )
      , Expr.epsilon
      , (Expr.tree (Pred.eq (Token.string "d"))
          3
        )
      , Expr.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false
