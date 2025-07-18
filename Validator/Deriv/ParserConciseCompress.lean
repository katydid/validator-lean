-- ParserConciseCompress is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a ParseTree.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- It does add compression for a small optimization, see lines marked with NEW

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Env
import Validator.Deriv.EnvTreeParserState
import Validator.Deriv.Leave

import Validator.Parser.ParseTree
import Validator.Parser.Parser
import Validator.Parser.Hint

namespace ParserConciseCompress

def deriveEnter [Env m] (xs: List Expr): m (List Expr) := do
  let token <- Parser.token
  let enters <- Enter.DeriveEnter.deriveEnter xs
  return IfExpr.evals enters token

def deriveLeave [Env m] (xs: List Expr) (cs: List Expr): m (List Expr) :=
  Leave.DeriveLeave.deriveLeave xs (List.map Expr.nullable cs)

def deriveValue [Env m] (xs: List Expr): m (List Expr) := do
  deriveLeave xs (<- deriveEnter xs)

partial def derive [Env m] (xs: List Expr): m (List Expr) := do
  if List.all xs Expr.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let childxs <- deriveEnter xs -- derive enter field
    let dchildxs <-
      match <- Parser.next with
      | Hint.value => deriveValue childxs -- derive child value
      | Hint.enter =>
        let (cchildxs, indices) <- Compress.compressM childxs -- NEW: compress
        let cdchildxs <- derive cchildxs -- derive children, until return from a Hint.leave
        Compress.expandM indices cdchildxs -- NEW: expand
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeave xs dchildxs -- derive leave field
    derive xsLeave -- deriv next
  | Hint.value => deriveValue xs >>= derive -- derive value and then derive next
  | Hint.enter =>
    let (cchildxs, indices) <- Compress.compressM xs -- NEW: compress
    let cdchildxs <- derive cchildxs -- derive children, until return from a Hint.leave
    let dchildxs <- Compress.expandM indices cdchildxs -- NEW: expand
    derive dchildxs -- derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate {m} [Env m] (x: Expr): m Bool := do
  let dxs <- derive [x]
  match dxs with
  | [dx] => return Expr.nullable dx
  | _ => throw "expected one expression"

def run (x: Expr) (t: ParseTree): Except String Bool :=
  EnvTreeParserState.run (validate x) t

open ParseTree (node)

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
