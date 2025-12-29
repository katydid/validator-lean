import Validator.Std.Hedge
import Validator.Std.List
import Validator.Std.Vec

import Validator.Pred.AnyEq
import Validator.Regex.Regex
import Validator.Regex.Elem
import Validator.Regex.Language
import Validator.Hedge.Types
import Validator.Hedge.Language

namespace Hedge.Grammar

def lookup {n: Nat} {φ: Type}
  (G: Grammar n φ) (ref: Fin n): Rule n φ :=
  Vec.get G.prods ref

def singleton (x: Rule 0 φ): Grammar 0 φ  :=
  Grammar.mk x #vec[]

def emptyset: Grammar 0 φ :=
  singleton Regex.emptyset

def emptystr: Grammar 0 φ :=
  singleton Regex.emptystr

def Rule.null (r: Rule n φ): Bool :=
  Regex.null r

def null (G: Grammar n φ): Bool :=
  Rule.null G.start

example : Grammar 5 (AnyEq.Pred String) := Grammar.mk
  -- start := ("html", Html)
  (start := Regex.symbol (AnyEq.Pred.eq "html", 0))
  -- production rules
  (prods := #vec[
    -- Html -> ("head", Head) · ("body", Body)
    Regex.concat
      (Regex.symbol (AnyEq.Pred.eq "head", 1))
      (Regex.symbol (AnyEq.Pred.eq "body", 2))
    -- Head -> ("title", Text) | ε
    , Regex.or
      (Regex.symbol (AnyEq.Pred.eq "title", 3))
      Regex.emptystr
    -- Body -> ("p", Text)*
    , Regex.star (Regex.symbol (AnyEq.Pred.eq "p", 3))
    -- Text -> (., Empty)
    , Regex.symbol (AnyEq.Pred.any, 4)
    -- Empty -> ε
    , Regex.emptystr
  ])

private def example_grammar: Grammar 1 (AnyEq.Pred Char) :=
  Grammar.mk
    (Regex.or Regex.emptystr (Regex.symbol (AnyEq.Pred.eq 'a', 0)))
    #vec[Regex.emptystr]

#guard
  example_grammar.lookup (Fin.mk 0 (by omega))
  = Regex.emptystr
