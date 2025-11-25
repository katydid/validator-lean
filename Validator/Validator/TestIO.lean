import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Validator.Validate

import Validator.Validator.Inst.TreeParserIO
import Validator.Validator.ValidateM

namespace TestIO

def validate {m} [DecidableEq α] [ValidateM m n α] (g: Grammar n (Pred α)) (x: Rule n (Pred α)): m Bool :=
  Validate.validate g x

unsafe def run [DecidableEq α] [Hashable α] (g: Grammar n (Pred α)) (t: Hedge.Node α): Except String Bool :=
  unsafeEIO (TreeParserIO.run' (n := n) (validate g g.start) t)

-- runTwice is used to check if the cache was hit on the second run
def runTwice [DecidableEq α] [Hashable α] [DecidableEq β] (f: TreeParserIO.Impl n α β) (t: Hedge.Node α): EIO String β := do
  let initial := TreeParserIO.Impl.mk (TreeParser.ParserState.mk' t)
  let (res1, updated) <- StateT.run f initial
  _ <- TreeParserIO.EIO.println "start second run"
  let res2 <- StateT.run' f (TreeParserIO.State.mk (TreeParser.ParserState.mk' t) updated.enter updated.leave)
  if res1 ≠ res2
  then throw "memoization changed result"
  else return res1

-- runTwice is used to check if the cache was hit on the second run
unsafe def runTwice' [DecidableEq α] [Hashable α] (g: Grammar n (Pred α)) (t: Hedge.Node α): Except String Bool :=
  unsafeEIO (runTwice (n := n) (validate g g.start) t)

open TokenTree (node)

-- #eval runTwice'
--   (Grammar.singleton Regex.emptyset)
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Grammar.mk (n := 1)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[Regex.emptystr]
--   )
--   (node "a" [])

-- #eval runTwice'
--   (Grammar.mk (n := 1)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[Regex.emptystr]
--   )
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Grammar.mk (n := 2)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[
--       (Regex.symbol (Pred.eq (Token.string "b"), 1))
--       , Regex.emptystr
--     ]
--   )
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Grammar.mk (n := 2)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[
--       (Regex.concat
--         (Regex.symbol (Pred.eq (Token.string "b"), 1))
--         (Regex.symbol (Pred.eq (Token.string "c"), 1))
--       )
--       , Regex.emptystr
--     ]
--   )
--   (node "a" [node "b" [], node "c" []])

-- #eval runTwice'
--   (Grammar.mk (n := 3)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[
--       (Regex.concat
--         (Regex.symbol (Pred.eq (Token.string "b"), 1))
--         (Regex.symbol (Pred.eq (Token.string "c"), 2))
--       )
--       , Regex.emptystr
--       , (Regex.symbol (Pred.eq (Token.string "d"), 1))
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- -- try to engage skip using emptyset, since it is unescapable
-- #eval runTwice'
--   (Grammar.mk (n := 1)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[Regex.emptyset]
--   )
--   (node "a" [node "b" []])

-- #eval runTwice'
--   (Grammar.mk (n := 4)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[
--       (Regex.concat
--         (Regex.symbol (Pred.eq (Token.string "b"), 3))
--         (Regex.symbol (Pred.eq (Token.string "c"), 2))
--       )
--       , Regex.emptystr
--       , (Regex.symbol (Pred.eq (Token.string "d"), 1))
--       , Regex.emptyset
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Grammar.mk (n := 2)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[
--       (Regex.concat
--         (Regex.symbol (Pred.eq (Token.string "b"), 1))
--         Regex.emptyset
--       )
--       , Regex.emptystr
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Grammar.mk (n := 3)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[
--       (Regex.concat
--         (Regex.symbol (Pred.eq (Token.string "b"), 1))
--         (Regex.symbol (Pred.eq (Token.string "c"), 2))
--       )
--       , Regex.emptystr
--       , Regex.emptyset
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])

-- #eval runTwice'
--   (Grammar.mk (n := 4)
--     (Regex.symbol (Pred.eq (Token.string "a"), 0))
--     #v[
--       (Regex.concat
--         (Regex.symbol (Pred.eq (Token.string "b"), 0))
--         (Regex.symbol (Pred.eq (Token.string "c"), 1))
--       )
--       , Regex.emptystr
--       , (Regex.symbol (Pred.eq (Token.string "d"), 2))
--       , Regex.emptyset
--     ]
--   )
--   (node "a" [node "b" [], node "c" [node "d" []]])
