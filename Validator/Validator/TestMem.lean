import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Parser.TokenTree

import Validator.Validator.Validate
import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemM
import Validator.Validator.Inst.TreeParserMemTestM

namespace TestMem

def validate {m} [DecidableEq φ] [ValidateM m (Hedge.Grammar.Symbol n φ) α]
  (G: Hedge.Grammar n φ) (Φ : φ → α → Bool)
  (x: Hedge.Grammar.Rule n φ): m Bool :=
  Validate.validate G Φ x

def run [DecidableEq α] [Hashable α] (G: Hedge.Grammar n (AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  TreeParserMemM.run' (n := n) (φ := AnyEq.Pred α) (validate G AnyEq.Pred.evalb G.start) t

-- Tests

def testCacheIsHitOnSecondRun
  [DecidableEq α] [Hashable α]
  (G: Hedge.Grammar n (AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  match TreeParserMemM.run (n := n) (φ := AnyEq.Pred α) (validate G AnyEq.Pred.evalb G.start) t with
  | EStateM.Result.error err _ => Except.error err
  | EStateM.Result.ok res1 state =>
    match TreeParserMemTestM.runPopulatedMem (n := n) (validate G AnyEq.Pred.evalb G.start) t state.enter state.leave with
    | EStateM.Result.error err _ => Except.error err
    | EStateM.Result.ok res2 _ =>
      if res1 ≠ res2
      then throw "memoization result doesn't match original"
      else return res2

-- A negaive test for the test above
-- This tests that given an empty cache the test does actually fail.
def testThatTestCacheBreaksWithEmptyCache
  [DecidableEq α] [Hashable α]
  (G: Hedge.Grammar n (AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  TreeParserMemTestM.run' (n := n) (φ := AnyEq.Pred α) (validate G AnyEq.Pred.evalb G.start) t

open TokenTree (node)

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [])
  = Except.ok true

#guard testThatTestCacheBreaksWithEmptyCache
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [])
  = Except.error "test cache miss"

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []])
  = Except.ok true

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq (Token.string "d"), 1))
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptyset]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 4)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 3))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq (Token.string "d"), 1))
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        Regex.emptyset
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false

#guard testCacheIsHitOnSecondRun
  (Hedge.Grammar.mk (n := 4)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 0))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq (Token.string "d"), 2))
      , Regex.emptyset
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok false
