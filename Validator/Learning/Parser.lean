-- Parser is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a ParseTree.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Parser.Hint
import Validator.Parser.Parser
import Validator.Parser.ParseTree
import Validator.Parser.TokenTree

import Validator.Derive.Enter
import Validator.Derive.Leave

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserM

namespace Parser

def deriveEnter [DecidableEq α] [ValidateM m α] (xs: Exprs α): m (Exprs α) := do
  let enters <- Enter.DeriveEnter.deriveEnter xs
  let token <- Parser.token
  return IfExpr.evals enters token

def deriveLeave [DecidableEq α] [ValidateM m α] (xs: Exprs α) (cs: Exprs α): m (Exprs α) :=
  Leave.DeriveLeave.deriveLeave xs (List.map Expr.nullable cs)

def deriveValue [DecidableEq α] [ValidateM m α] (xs: Exprs α): m (Exprs α) := do
  deriveEnter xs >>= deriveLeave xs

-- TODO: Is it possible to have a Parser type that can be proved to be of the correct shape, and have not expection throwing
-- for example: can you prove that your Parser will never return an Hint.leave after returning a Hint.field.
-- This class can be called the LawfulParser.
partial def derive [DecidableEq α] [ValidateM m α] (xs: Exprs α): m (Exprs α) := do
  if List.all xs Expr.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let childxs <- deriveEnter xs -- derive enter field
    let dchildxs <-
      match <- Parser.next with
      | Hint.value => deriveValue childxs -- derive child value
      | Hint.enter => derive childxs -- derive children, until return from a Hint.leave
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeave xs dchildxs -- derive leave field
    derive xsLeave -- deriv next
  | Hint.value => deriveValue xs >>= derive -- derive value and then derive next
  | Hint.enter => derive xs >>= derive -- derive children, until return from a Hint.leave and then derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate {m} [DecidableEq α] [ValidateM m α] (x: Expr α): m Bool := do
  let dxs <- derive [x]
  match dxs with
  | [dx] => return Expr.nullable dx
  | _ => throw "expected one expression"

def run [DecidableEq α] (x: Expr α) (t: ParseTree α): Except String Bool :=
  TreeParserM.run' (validate x) t

-- Tests

open TokenTree (node)

#guard run
  Expr.emptyset
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (node "a" [node "b" []]) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        Expr.epsilon
      )
    )
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        (Expr.tree (Pred.eq (Token.string "d"))
          Expr.epsilon
        )
      )
    )
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    Expr.emptyset
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.emptyset
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        (Expr.tree (Pred.eq (Token.string "d"))
          Expr.epsilon
        )
      )
    )
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      Expr.emptyset
    )
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        Expr.emptyset
      )
    )
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        (Expr.tree (Pred.eq (Token.string "d"))
          Expr.emptyset
        )
      )
    )
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false
