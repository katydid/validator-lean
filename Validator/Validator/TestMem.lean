import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Validator.Validate
import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemM
import Validator.Validator.Inst.TreeParserMemTestM

namespace TestMem

def validate {m} [DecidableEq α] [ValidateM m μ α] (g: Grammar μ α Pred) (x: Rule μ α Pred): m Bool :=
  Validate.validate g x

def run [DecidableEq α] [Hashable α] (g: Grammar μ α Pred) (t: Hedge.Node α): Except String Bool :=
  TreeParserMemM.run' (μ := μ) (validate g g.start) t

-- Tests

def testCacheIsHitOnSecondRun
  [DecidableEq α] [Hashable α]
  (g: Grammar μ α Pred) (t: Hedge.Node α): Except String Bool :=
  match TreeParserMemM.run (μ := μ) (validate g g.start) t with
  | EStateM.Result.error err _ => Except.error err
  | EStateM.Result.ok res1 state =>
    match TreeParserMemTestM.runPopulatedMem (μ := μ) (validate g g.start) t state.enter state.leave with
    | EStateM.Result.error err _ => Except.error err
    | EStateM.Result.ok res2 _ =>
      if res1 ≠ res2
      then throw "memoization result doesn't match original"
      else return res2

-- A negaive test for the test above
-- This tests that given an empty cache the test does actually fail.
def testThatTestCacheBreaksWithEmptyCache
  [DecidableEq α] [Hashable α]
  (g: Grammar μ α Pred) (t: Hedge.Node α): Except String Bool :=
  TreeParserMemTestM.run' (μ := μ) (validate g g.start) t

open TokenTree (node)

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [])
  = Except.ok true

#guard testThatTestCacheBreaksWithEmptyCache
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [])
  = Except.error "test cache miss"

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []])
  = Except.ok true

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.eq (Token.string "d"), 1))
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptyset]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 4)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 3))
        (Regex.symbol (Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.eq (Token.string "d"), 1))
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        Regex.emptyset
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (μ := 4)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 0))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.eq (Token.string "d"), 2))
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false
