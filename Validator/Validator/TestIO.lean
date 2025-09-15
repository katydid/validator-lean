import Validator.Std.ParseTree
import Validator.Parser.TokenTree

import Validator.Validator.Validate

import Validator.Validator.Inst.TreeParserIO
import Validator.Validator.ValidateM

namespace TestIO

def validate {m} [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (x: Expr μ α): m Bool :=
  Validate.validate g x

unsafe def run [DecidableEq α] [Hashable α] (g: Expr.Grammar μ α) (t: ParseTree α): Except String Bool :=
  unsafeEIO (TreeParserIO.run' (μ := μ) (validate g g.lookup0) t)

-- runTwice is used to check if the cache was hit on the second run
def runTwice [DecidableEq α] [Hashable α] [DecidableEq β] (f: TreeParserIO.Impl μ α β) (t: ParseTree α): EIO String β := do
  let initial := TreeParserIO.Impl.mk (TreeParser.ParserState.mk' t)
  let (res1, updated) <- StateT.run f initial
  _ <- TreeParserIO.EIO.println "start second run"
  let res2 <- StateT.run' f (TreeParserIO.State.mk (TreeParser.ParserState.mk' t) updated.enter updated.leave)
  if res1 ≠ res2
  then throw "memoization changed result"
  else return res1

-- runTwice is used to check if the cache was hit on the second run
unsafe def runTwice' [DecidableEq α] [Hashable α] (g: Expr.Grammar μ α) (t: ParseTree α): Except String Bool :=
  unsafeEIO (runTwice (μ := μ) (validate g g.lookup0) t)

open TokenTree (node)

-- #eval runTwice'
--   (Expr.Grammar.singleton Expr.emptyset)
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 2)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[Expr.epsilon]
--   )
--   (node "a" [])

-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 2)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[Expr.epsilon]
--   )
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 3)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[
--       (Expr.tree (Pred.eq (Token.string "b")) 2)
--       , Expr.epsilon
--     ]
--   )
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 3)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[
--       (Expr.concat
--         (Expr.tree (Pred.eq (Token.string "b")) 2)
--         (Expr.tree (Pred.eq (Token.string "c")) 2)
--       )
--       , Expr.epsilon
--     ]
--   )
--   (node "a" [node "b" [], node "c" []])

-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 4)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[
--       (Expr.concat
--         (Expr.tree (Pred.eq (Token.string "b")) 2)
--         (Expr.tree (Pred.eq (Token.string "c")) 3)
--       )
--       , Expr.epsilon
--       , (Expr.tree (Pred.eq (Token.string "d")) 2)
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- -- try to engage skip using emptyset, since it is unescapable
-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 2)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[Expr.emptyset]
--   )
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 5)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[
--       (Expr.concat
--         (Expr.tree (Pred.eq (Token.string "b")) 4)
--         (Expr.tree (Pred.eq (Token.string "c")) 3)
--       )
--       , Expr.epsilon
--       , (Expr.tree (Pred.eq (Token.string "d")) 2)
--       , Expr.emptyset
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 3)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[
--       (Expr.concat
--         (Expr.tree (Pred.eq (Token.string "b"))
--           2
--         )
--         Expr.emptyset
--       )
--       , Expr.epsilon
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Expr.Grammar.mk (μ := 4)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[
--       (Expr.concat
--         (Expr.tree (Pred.eq (Token.string "b"))
--           2
--         )
--         (Expr.tree (Pred.eq (Token.string "c"))
--           3
--         )
--       )
--       , Expr.epsilon
--       , Expr.emptyset
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

--  #eval runTwice'
--    (Expr.Grammar.mk (μ := 5)
--     (Expr.tree (Pred.eq (Token.string "a")) 1)
--     #v[
--       (Expr.concat
--         (Expr.tree (Pred.eq (Token.string "b"))
--           1
--         )
--         (Expr.tree (Pred.eq (Token.string "c"))
--           2
--         )
--       )
--       , Expr.epsilon
--       , (Expr.tree (Pred.eq (Token.string "d"))
--           3
--         )
--       , Expr.emptyset
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])
