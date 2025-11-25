import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Validator.Validate
import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemLogM
import Validator.Validator.Inst.TreeParserMemTestM

namespace TestMemLog

def validate {m} [DecidableEq α] [ValidateM m n α] (g: Grammar n (Pred α)) (x: Rule n (Pred α)): m Bool :=
  Validate.validate g x

def run
  [DecidableEq α] [Hashable α]
  (g: Grammar n (Pred α)) (t: Hedge.Node α): (List String × Except String Bool) :=
  TreeParserMemLogM.run' (n := n) (validate g g.start) t

-- Tests

def testCacheIsHitOnSecondRun
  [DecidableEq α] [Hashable α]
  (g: Grammar n (Pred α)) (t: Hedge.Node α): (List String × Except String Bool) :=
  match TreeParserMemLogM.run (n := n) (validate g g.start) t with
  | EStateM.Result.error err state1 => (state1.logs, Except.error err)
  | EStateM.Result.ok res1 state1 =>
    match TreeParserMemLogM.runPopulatedMem (n := n) (validate g g.start) t state1.enter state1.leave with
    | EStateM.Result.error err state2 => (state1.logs ++ state2.logs, Except.error err)
    | EStateM.Result.ok res2 state2 =>
      if res1 ≠ res2
      then (state1.logs ++ ["start second run"] ++ state2.logs, Except.error "memoization result doesn't match original")
      else (state1.logs ++ ["start second run"] ++ state2.logs, return res2)

-- A negaive test for the test above
-- This tests that given an empty cache the test does actually fail.
def testThatTestCacheBreaksWithEmptyCache
  [DecidableEq α] [Hashable α]
  (g: Grammar n (Pred α)) (t: Hedge.Node α): Except String Bool :=
  TreeParserMemTestM.run' (n := n) (validate g g.start) t

open TokenTree (node)

#guard testCacheIsHitOnSecondRun
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  (
    [
      "skip",
      "start second run",
      "skip"
    ],
    Except.ok false
  )

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" []) =
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "next",
      "next",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "next",
      "next"
    ],
    Except.ok true
  )

#guard testThatTestCacheBreaksWithEmptyCache
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" []) =
  Except.error "test cache miss"

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "cache miss",
      "skip",
      "skip",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "cache hit",
      "skip",
      "skip",
    ],
    Except.ok false
  )

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []]) =
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "cache miss",
      "next",
      "next",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "cache hit",
      "next",
      "next",
    ],
    Except.ok true
  )

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "next",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "next",
      "cache miss",
      "next",
      "next",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "next",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "next",
      "cache hit",
      "next",
      "next",
    ],
    Except.ok true
  )

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 3)
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
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "next",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "next",
      "token",
      "cache miss",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "cache miss",
      "next",
      "cache miss",
      "next",
      "next",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "next",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "next",
      "token",
      "cache hit",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "cache hit",
      "next",
      "cache hit",
      "next",
      "next",
    ],
    Except.ok true
  )

-- try to engage skip using emptyset, since it is unescapable
#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "cache miss",
      "skip",
      "skip",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "cache hit",
      "skip",
      "skip",
    ],
    Except.ok false
  )

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 4)
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
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "next",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "skip",
      "cache miss",
      "skip",
      "skip",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "next",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "skip",
      "cache hit",
      "skip",
      "skip",
    ],
    Except.ok false
  )

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 2)
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
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "next",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "skip",
      "cache miss",
      "skip",
      "skip",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "next",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "skip",
      "cache hit",
      "skip",
      "skip",
    ],
    Except.ok false
  )

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 3)
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
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  (
    [
      "next",
      "next",
      "token",
      "cache miss",
      "next",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "next",
      "token",
      "cache miss",
      "next",
      "token",
      "cache miss",
      "cache miss",
      "cache miss",
      "skip",
      "cache miss",
      "skip",
      "skip",
      "start second run",
      "next",
      "next",
      "token",
      "cache hit",
      "next",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "next",
      "token",
      "cache hit",
      "next",
      "token",
      "cache hit",
      "cache hit",
      "cache hit",
      "skip",
      "cache hit",
      "skip",
      "skip",
    ],
    Except.ok false
  )

#guard testCacheIsHitOnSecondRun
  (Grammar.mk (n := 4)
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
  = (
    [ "next", "next", "token", "cache miss", "next", "next", "token"
    , "cache miss", "cache miss", "skip", "cache miss", "skip", "skip"
    , "start second run"
    , "next", "next", "token", "cache hit", "next", "next", "token"
    , "cache hit", "cache hit", "skip", "cache hit", "skip", "skip"],
     Except.ok false
  )
