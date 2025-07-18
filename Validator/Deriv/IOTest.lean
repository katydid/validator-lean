import Validator.Parser.ParseTree

import Validator.Deriv.Env
import Validator.Deriv.EnvTreeParserIO
import Validator.Deriv.ParserConciseCompress

namespace IOTest

def validate {m} [Env m] (x: Expr): m Bool :=
  ParserConciseCompress.validate x

unsafe def run (x: Expr) (t: ParseTree): Except String Bool :=
  unsafeEIO (EnvTreeParserIO.run (validate x) t)

-- runTwice is used to check if the cache was hit on the second run
unsafe def runTwice (x: Expr) (t: ParseTree): Except String Bool :=
  unsafeEIO (EnvTreeParserIO.runTwice (validate x) t)

open ParseTree (field)

#eval run
  Expr.emptyset
  (field "a" [field "b" [], field "c" [field "d" []]])

#eval run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" [])

#eval run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" [field "b" []])

#eval run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (field "a" [field "b" []])

#eval run
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
  (field "a" [field "b" [], field "c" []])

#eval run
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
  (field "a" [field "b" [], field "c" [field "d" []]])

-- try to engage skip using emptyset, since it is unescapable
#eval run
  (Expr.tree (Pred.eq (Token.string "a"))
    Expr.emptyset
  )
  (field "a" [field "b" []])

#eval run
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
  (field "a" [field "b" [], field "c" [field "d" []]])

#eval run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      Expr.emptyset
    )
  )
  (field "a" [field "b" [], field "c" [field "d" []]])

#eval run
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
  (field "a" [field "b" [], field "c" [field "d" []]])

#eval runTwice
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
  (field "a" [field "b" [], field "c" [field "d" []]])
