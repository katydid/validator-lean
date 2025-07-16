-- ParserConcise is a memoizable version of the validation algorithm.
-- This version of the algorithm uses a Parser instead of a LTree.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

import Validator.Parser.Parser
import Validator.Parser.Hint

import Validator.Parser.LTree

namespace LTreeConcise

def derivEnter [Monad m] [MonadExcept String m] [Parser m] (xs: List Expr): m (List Expr) := do
  return IfExpr.evals (Enter.enters xs) (<- Parser.token)

def derivLeave [Monad m] [MonadExcept String m] (xs: List Expr) (cs: List Expr): m (List Expr) :=
  Leave.leaves xs (List.map Expr.nullable cs)

def derivValue [Monad m] [MonadExcept String m] [Parser m] (xs: List Expr): m (List Expr) := do
  derivLeave xs (<- derivEnter xs)

partial def deriv [Monad m] [MonadExcept String m] [Parser m] (xs: List Expr): m (List Expr) := do
  if List.all xs Expr.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let xsEnter <- derivEnter xs -- derive enter field
    let xsChild <-
      match <- Parser.next with
      | Hint.value => derivValue xsEnter -- derive child value
      | Hint.enter => deriv xsEnter -- derive children, until return from a Hint.leave
      | hint => throw s!"unexpected {hint}"
    let xsLeave := <- derivLeave xs xsChild -- derive leave field
    deriv xsLeave -- deriv next
  | Hint.value => derivValue xs >>= deriv -- derive value and then derive next
  | Hint.enter => deriv xs >>= deriv -- derive children, until return from a Hint.leave and then derive next
  | Hint.leave => return xs -- never happens at the top
  | Hint.eof => return xs -- only happens at the top

def validate [Monad m] [MonadExcept String m] [Parser m] (x: Expr): m Bool := do
  let dxs <- deriv [x]
  match dxs with
  | [dx] => return Expr.nullable dx
  | _ => throw "expected one expression"

def run (x: Expr) (t: LTree): Except String Bool :=
  LTree.LTreeParser.run (validate x) t

#guard run
  Expr.emptyset
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (LTree.node "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (LTree.node "a" [LTree.node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (LTree.node "a" [LTree.node "b" []]) =
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
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" []]) =
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
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    Expr.emptyset
  )
  (LTree.node "a" [LTree.node "b" []]) =
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
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
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
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
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
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
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
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok false
