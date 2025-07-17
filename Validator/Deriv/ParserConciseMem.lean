import Validator.Parser.ParseTree

import Validator.Deriv.Env
import Validator.Deriv.ParserConcise

namespace ParserConciseMem

def validate {m} [Env m] (x: Expr): m Bool :=
  ParserConcise.validate x

def run' (x: Env.TreeMem α) (t: ParseTree): Except String α :=
  StateT.run' x (Env.TreeMem.mk (ParseTree.TreeParser.mk' t))

def run (x: Expr) (t: ParseTree): Except String Bool :=
  run' (validate x) t

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
