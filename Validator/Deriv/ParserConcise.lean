-- ParserConcise is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a ParseTree.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Env
import Validator.Deriv.Leave

import Validator.Parser.Hint
import Validator.Parser.Parser
import Validator.Parser.ParseTree

namespace ParserConcise

def deriveEnter [Env m] (xs: List Expr): m (List Expr) := do
  let token <- Parser.token
  let enters <- Enter.DeriveEnters.deriveEnters xs
  return IfExpr.evals enters token

def deriveLeave [Env m] (xs: List Expr) (cs: List Expr): m (List Expr) :=
  Leave.DeriveLeaves.deriveLeaves xs (List.map Expr.nullable cs)

def deriveValue [Env m] (xs: List Expr): m (List Expr) := do
  deriveLeave xs (<- deriveEnter xs)

partial def derive [Env m] (xs: List Expr): m (List Expr) := do
  if List.all xs Expr.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let xsEnter <- deriveEnter xs -- derive enter field
    let xsChild <-
      match <- Parser.next with
      | Hint.value => deriveValue xsEnter -- derive child value
      | Hint.enter => derive xsEnter -- derive children, until return from a Hint.leave
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeave xs xsChild -- derive leave field
    derive xsLeave -- deriv next
  | Hint.value => deriveValue xs >>= derive -- derive value and then derive next
  | Hint.enter => derive xs >>= derive -- derive children, until return from a Hint.leave and then derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate {m} [Env m] (x: Expr): m Bool := do
  let dxs <- derive [x]
  match dxs with
  | [dx] => return Expr.nullable dx
  | _ => throw "expected one expression"

def run (x: Expr) (t: ParseTree): Except String Bool :=
  ParseTree.TreeParser.run (validate x) t

#guard run
  Expr.emptyset
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" [ParseTree.node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (ParseTree.node "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (ParseTree.node "a" [ParseTree.node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (ParseTree.node "a" [ParseTree.node "b" []]) =
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
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" []]) =
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
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" [ParseTree.node "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    Expr.emptyset
  )
  (ParseTree.node "a" [ParseTree.node "b" []]) =
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
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" [ParseTree.node "d" []]]) =
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
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" [ParseTree.node "d" []]]) =
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
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" [ParseTree.node "d" []]]) =
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
  (ParseTree.node "a" [ParseTree.node "b" [], ParseTree.node "c" [ParseTree.node "d" []]]) =
  Except.ok false
