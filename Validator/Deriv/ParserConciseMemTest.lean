import Validator.Parser.ParseTree

import Validator.Deriv.Env
import Validator.Deriv.EnvTreeParserStateWithMem
import Validator.Deriv.EnvTreeParserStateWithMemTest
import Validator.Deriv.ParserConcise

namespace ParserConciseMemTest

def validate {m} [Env m] (x: Expr): m Bool :=
  ParserConcise.validate x

def run (x: Expr) (t: ParseTree): Except String Bool :=
  EnvTreeParserStateWithMem.run (validate x) t

def testCacheIsHitOnSecondRun (x: Expr) (t: ParseTree): Except String Bool :=
  match EnvTreeParserStateWithMem.run' (validate x) t with
  | EStateM.Result.error err _ => Except.error err
  | EStateM.Result.ok res1 (populatedEnter, populatedLeave) =>
    match EnvTreeParserStateWithMemTest.run' (validate x) t populatedEnter populatedLeave with
    | EStateM.Result.error err _ => Except.error err
    | EStateM.Result.ok res2 _ =>
      if res1 ≠ res2
      then throw "memoization result doesn't match original"
      else return res2

-- A negaive test for the test above
-- This tests that given an empty cache the test does actually fail.
def testThatTestCacheBreaksWithEmptyCache (x: Expr) (t: ParseTree): Except String Bool :=
  match EnvTreeParserStateWithMemTest.run' (validate x) t MemEnter.EnterMap.mk MemLeave.LeaveMap.mk with
  | EStateM.Result.error err _ => Except.error err
  | EStateM.Result.ok res _ => Except.ok res

open ParseTree (field)

#guard testCacheIsHitOnSecondRun
  Expr.emptyset
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok false

#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" []) =
  Except.ok true

#guard testThatTestCacheBreaksWithEmptyCache
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" []) =
  Except.error "test cache miss"

#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" [field "b" []]) =
  Except.ok false

#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (field "a" [field "b" []]) =
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
  (field "a" [field "b" [], field "c" []]) =
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
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard testCacheIsHitOnSecondRun
  (Expr.tree (Pred.eq (Token.string "a"))
    Expr.emptyset
  )
  (field "a" [field "b" []]) =
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
  (field "a" [field "b" [], field "c" [field "d" []]]) =
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
  (field "a" [field "b" [], field "c" [field "d" []]]) =
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
  (field "a" [field "b" [], field "c" [field "d" []]]) =
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
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok false
