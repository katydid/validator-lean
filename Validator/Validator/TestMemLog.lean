import Validator.Parser.ParseTree

import Validator.Validator.Validate
import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemLogM
import Validator.Validator.Inst.TreeParserMemTestM

namespace TestMemLog

def validate {m} [ValidateM m] (x: Expr): m Bool :=
  Validate.validate x

def run (x: Expr) (t: ParseTree): (List String × Except String Bool) :=
  TreeParserMemLogM.run' (validate x) t

-- Tests

def testCacheIsHitOnSecondRun (x: Expr) (t: ParseTree): (List String × Except String Bool) :=
  match TreeParserMemLogM.run (validate x) t with
  | EStateM.Result.error err state1 => (state1.logs, Except.error err)
  | EStateM.Result.ok res1 state1 =>
    match TreeParserMemLogM.runPopulatedMem (validate x) t state1.enter state1.leave with
    | EStateM.Result.error err state2 => (state1.logs ++ state2.logs, Except.error err)
    | EStateM.Result.ok res2 state2 =>
      if res1 ≠ res2
      then (state1.logs ++ ["start second run"] ++ state2.logs, Except.error "memoization result doesn't match original")
      else (state1.logs ++ ["start second run"] ++ state2.logs, return res2)

-- A negaive test for the test above
-- This tests that given an empty cache the test does actually fail.
def testThatTestCacheBreaksWithEmptyCache (x: Expr) (t: ParseTree): Except String Bool :=
  TreeParserMemTestM.run' (validate x) t

open ParseTree (node)

#guard testCacheIsHitOnSecondRun
  Expr.emptyset
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
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
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
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" []) =
  Except.error "test cache miss"

#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
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
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
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
  (Expr.tree (Pred.eq (Token.string "a"))
    Expr.emptyset
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
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      Expr.emptyset
    )
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
