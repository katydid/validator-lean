import Validator.Parser.ParseTree

import Validator.Validator.Validate

import Validator.Validator.Inst.TreeParserIO
import Validator.Validator.ValidateM

namespace TestIO

def validate {m} [ValidateM m] (x: Expr): m Bool :=
  Validate.validate x

unsafe def run (x: Expr) (t: ParseTree): Except String Bool :=
  unsafeEIO (TreeParserIO.run' (validate x) t)

-- runTwice is used to check if the cache was hit on the second run
def runTwice [DecidableEq α] (f: TreeParserIO.Impl α) (t: ParseTree): EIO String α := do
  let initial := TreeParserIO.Impl.mk (TreeParser.TreeParser.mk t)
  let (res1, updated) <- StateT.run f initial
  _ <- TreeParserIO.EIO.println "start second run"
  let res2 <- StateT.run' f (TreeParserIO.State.mk (TreeParser.TreeParser.mk t) updated.enter updated.leave)
  if res1 ≠ res2
  then throw "memoization changed result"
  else return res1

-- runTwice is used to check if the cache was hit on the second run
unsafe def runTwice' (x: Expr) (t: ParseTree): Except String Bool :=
  unsafeEIO (runTwice (validate x) t)

open ParseTree (node)

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
