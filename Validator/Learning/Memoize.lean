import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Parser.TokenTree

import Validator.Validator.ValidateM
import Validator.Validator.Inst.TreeParserMemM

import Validator.Learning.Parser

namespace Memoize

def validate {m} [DecidableEq φ] [ValidateM m n φ α]
  (G: Grammar n φ) (Φ : φ → α → Bool)
  (x: Rule n φ): m Bool :=
  Parser.validate G Φ x

def run [DecidableEq α] [Hashable α] (G: Grammar n (AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  TreeParserMemM.run' (n := n) (φ := AnyEq.Pred α) (validate G AnyEq.Pred.evalb G.start) t

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Grammar.mk (n := 3)
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
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptyset]
  )
  (node "a" [node "b" []])
  = Except.ok false

#guard run
  (Grammar.mk (n := 4)
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

#guard run
  (Grammar.mk (n := 2)
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

#guard run
  (Grammar.mk (n := 3)
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

#guard run
  (Grammar.mk (n := 4)
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
