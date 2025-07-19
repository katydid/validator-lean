import Validator.Parser.ParseTree

import Validator.Validator.Validate

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemM
import Validator.Validator.Inst.TreeParserMemTestM

namespace TestMemoize

def validate {m} [ValidateM m] (x: Expr): m Bool :=
  Validate.validate x

def run (x: Expr) (t: ParseTree): Except String Bool :=
  TreeParserMemM.run (validate x) t

-- Tests

def testCacheIsHitOnSecondRun (x: Expr) (t: ParseTree): Except String Bool :=
  match TreeParserMemM.run' (validate x) t with
  | EStateM.Result.error err _ => Except.error err
  | EStateM.Result.ok res1 (populatedEnter, populatedLeave) =>
    match TreeParserMemTestM.run' (validate x) t populatedEnter populatedLeave with
    | EStateM.Result.error err _ => Except.error err
    | EStateM.Result.ok res2 _ =>
      if res1 ≠ res2
      then throw "memoization result doesn't match original"
      else return res2

-- A negaive test for the test above
-- This tests that given an empty cache the test does actually fail.
def testThatTestCacheBreaksWithEmptyCache (x: Expr) (t: ParseTree): Except String Bool :=
  match TreeParserMemTestM.run' (validate x) t MemEnter.EnterMap.mk MemLeave.LeaveMap.mk with
  | EStateM.Result.error err _ => Except.error err
  | EStateM.Result.ok res _ => Except.ok res

open ParseTree (node)

#guard testCacheIsHitOnSecondRun
  Expr.emptyset
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" []) =
  Except.ok true

#guard testThatTestCacheBreaksWithEmptyCache
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" []) =
  Except.error "test cache miss"

#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" [node "b" []]) =
  Except.ok false

#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (node "a" [node "b" []]) =
  Except.ok true

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
  Except.ok true

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
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a"))
    Expr.emptyset
  )
  (node "a" [node "b" []]) =
  Except.ok false

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
  Except.ok false

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
  Except.ok false

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
  Except.ok false

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
  Except.ok false
