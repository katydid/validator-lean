-- ParserConciseCompress is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a Hedge.Node.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- It does add compression for a small optimization, see lines marked with NEW

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter
import Validator.Derive.Leave

import Validator.Std.Hedge
import Validator.Parser.TokenTree
import Validator.Parser.Parser
import Validator.Parser.Hint

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemM

namespace Validate

def deriveEnter [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (xs: Exprs μ α): m (Exprs μ α) := do
  let token <- Parser.token
  let enters <- Enter.DeriveEnter.deriveEnter xs
  return IfExpr.evals g enters token

def deriveLeaveM [ValidateM m μ α] (xs: Exprs μ α) (cs: Exprs μ α): m (Exprs μ α) :=
  Leave.DeriveLeaveM.deriveLeaveM xs (List.map Expr.nullable cs)

def deriveValue [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (xs: Exprs μ α): m (Exprs μ α) := do
  deriveLeaveM xs (<- deriveEnter g xs)

partial def derive [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (xs: Exprs μ α): m (Exprs μ α) := do
  if List.all xs Expr.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let childxs <- deriveEnter g xs -- derive enter field
    let dchildxs <-
      match <- Parser.next with
      | Hint.value => deriveValue g childxs -- derive child value
      | Hint.enter =>
        let (cchildxs, indices) <- Compress.compressM childxs -- NEW: compress
        let cdchildxs <- derive g cchildxs -- derive children, until return from a Hint.leave
        Compress.expandM indices cdchildxs -- NEW: expand
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeaveM xs dchildxs -- derive leave field
    derive g xsLeave -- deriv next
  | Hint.value => deriveValue g xs >>= derive g -- derive value and then derive next
  | Hint.enter =>
    let (cchildxs, indices) <- Compress.compressM xs -- NEW: compress
    let cdchildxs <- derive g cchildxs -- derive children, until return from a Hint.leave
    let dchildxs <- Compress.expandM indices cdchildxs -- NEW: expand
    derive g dchildxs -- derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate {m} {μ: Nat} {α: Type} [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (x: Expr μ α): m Bool := do
  let dxs <- derive g [x]
  match dxs with
  | [dx] => return Expr.nullable dx
  | _ => throw "expected one expression"

def run {μ: Nat} {α: Type} [DecidableEq α] [Hashable α] (g: Expr.Grammar μ α) (t: Hedge.Node α): Except String Bool :=
  TreeParserMemM.run' (μ := μ) (validate g g.lookup0) t

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
