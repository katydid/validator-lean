import Validator.Parser.ParseTree
import Validator.Parser.TokenTree

import Validator.Validator.Validate

import Validator.Validator.Inst.TreeParserIO
import Validator.Validator.ValidateM

namespace TestIO

def validate {m} [DecidableEq α] [ValidateM m α] (x: Expr α): m Bool :=
  Validate.validate x

unsafe def run [DecidableEq α] [Hashable α] (x: Expr α) (t: ParseTree α): Except String Bool :=
  unsafeEIO (TreeParserIO.run' (validate x) t)

-- runTwice is used to check if the cache was hit on the second run
def runTwice [DecidableEq α] [Hashable α] [DecidableEq β] (f: TreeParserIO.Impl α β) (t: ParseTree α): EIO String β := do
  let initial := TreeParserIO.Impl.mk (TreeParser.ParserState.mk' t)
  let (res1, updated) <- StateT.run f initial
  _ <- TreeParserIO.EIO.println "start second run"
  let res2 <- StateT.run' f (TreeParserIO.State.mk (TreeParser.ParserState.mk' t) updated.enter updated.leave)
  if res1 ≠ res2
  then throw "memoization changed result"
  else return res1

-- runTwice is used to check if the cache was hit on the second run
unsafe def runTwice' [DecidableEq α] [Hashable α] (x: Expr α) (t: ParseTree α): Except String Bool :=
  unsafeEIO (runTwice (validate x) t)

open TokenTree (node)

-- #eval runTwice'
--   Expr.emptyset
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
--   (node "a" [])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a"))
--     (Expr.tree (Pred.eq (Token.string "b"))
--       Expr.epsilon
--     )
--   )
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a"))
--     (Expr.concat
--       (Expr.tree (Pred.eq (Token.string "b"))
--         Expr.epsilon
--       )
--       (Expr.tree (Pred.eq (Token.string "c"))
--         Expr.epsilon
--       )
--     )
--   )
--   (node "a" [node "b" [], node "c" []])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a"))
--     (Expr.concat
--       (Expr.tree (Pred.eq (Token.string "b"))
--         Expr.epsilon
--       )
--       (Expr.tree (Pred.eq (Token.string "c"))
--         (Expr.tree (Pred.eq (Token.string "d"))
--           Expr.epsilon
--         )
--       )
--     )
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- -- try to engage skip using emptyset, since it is unescapable
-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a"))
--     Expr.emptyset
--   )
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a"))
--     (Expr.concat
--       (Expr.tree (Pred.eq (Token.string "b"))
--         Expr.emptyset
--       )
--       (Expr.tree (Pred.eq (Token.string "c"))
--         (Expr.tree (Pred.eq (Token.string "d"))
--           Expr.epsilon
--         )
--       )
--     )
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a"))
--     (Expr.concat
--       (Expr.tree (Pred.eq (Token.string "b"))
--         Expr.epsilon
--       )
--       Expr.emptyset
--     )
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a"))
--     (Expr.concat
--       (Expr.tree (Pred.eq (Token.string "b"))
--         Expr.epsilon
--       )
--       (Expr.tree (Pred.eq (Token.string "c"))
--         Expr.emptyset
--       )
--     )
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Expr.tree (Pred.eq (Token.string "a"))
--     (Expr.concat
--       (Expr.tree (Pred.eq (Token.string "b"))
--         Expr.epsilon
--       )
--       (Expr.tree (Pred.eq (Token.string "c"))
--         (Expr.tree (Pred.eq (Token.string "d"))
--           Expr.emptyset
--         )
--       )
--     )
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])
