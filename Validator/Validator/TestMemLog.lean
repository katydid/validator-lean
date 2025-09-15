import Validator.Std.ParseTree
import Validator.Parser.TokenTree

import Validator.Validator.Validate
import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemLogM
import Validator.Validator.Inst.TreeParserMemTestM

namespace TestMemLog

def validate {m} [DecidableEq α] [ValidateM m μ α] (g: Expr.Grammar μ α) (x: Expr μ α): m Bool :=
  Validate.validate g x

def run
  [DecidableEq α] [Hashable α]
  (g: Expr.Grammar μ α) (t: ParseTree α): (List String × Except String Bool) :=
  TreeParserMemLogM.run' (μ := μ) (validate g g.lookup0) t

-- Tests

def testCacheIsHitOnSecondRun
  [DecidableEq α] [Hashable α]
  (g: Expr.Grammar μ α) (t: ParseTree α): (List String × Except String Bool) :=
  match TreeParserMemLogM.run (μ := μ) (validate g g.lookup0) t with
  | EStateM.Result.error err state1 => (state1.logs, Except.error err)
  | EStateM.Result.ok res1 state1 =>
    match TreeParserMemLogM.runPopulatedMem (μ := μ) (validate g g.lookup0) t state1.enter state1.leave with
    | EStateM.Result.error err state2 => (state1.logs ++ state2.logs, Except.error err)
    | EStateM.Result.ok res2 state2 =>
      if res1 ≠ res2
      then (state1.logs ++ ["start second run"] ++ state2.logs, Except.error "memoization result doesn't match original")
      else (state1.logs ++ ["start second run"] ++ state2.logs, return res2)

-- A negaive test for the test above
-- This tests that given an empty cache the test does actually fail.
def testThatTestCacheBreaksWithEmptyCache
  [DecidableEq α] [Hashable α]
  (g: Expr.Grammar μ α) (t: ParseTree α): Except String Bool :=
  TreeParserMemTestM.run' (μ := μ) (validate g g.lookup0) t

open TokenTree (node)

#guard testCacheIsHitOnSecondRun
  (Expr.Grammar.singleton Expr.emptyset)
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
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
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
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" []) =
  Except.error "test cache miss"

#guard testCacheIsHitOnSecondRun
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
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
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.tree (Pred.eq (Token.string "b")) 2)
      , Expr.epsilon
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
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.emptyset]
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
  = (
    [ "next", "next", "token", "cache miss", "next", "next", "token"
    , "cache miss", "cache miss", "skip", "cache miss", "skip", "skip"
    , "start second run"
    , "next", "next", "token", "cache hit", "next", "next", "token"
    , "cache hit", "cache hit", "skip", "cache hit", "skip", "skip"],
     Except.ok false
  )
