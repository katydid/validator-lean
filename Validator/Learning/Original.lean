-- Original is the original derivative algorithm that runs on a labelled tree.
-- It is intended to be used for explanation purposes.
-- This version cannot be memoized effectively, but it is the easiest version to understand.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Grammar
import Validator.Expr.Pred
import Validator.Expr.Regex

namespace Original

-- foldLoop is a more readable version of List.foldl for imperative programmers:
-- Imperative programmers can imagine that `Id (Expr α)` = `Expr α`, because it does.
-- The Id wrapper just adds a monad wrapper to enable the do notation, so that we can use the for loop in Lean.
private def foldLoop (deriv: Rule n (Pred α) -> Hedge.Node α -> Rule n (Pred α)) (start: Rule n (Pred α)) (hedge: Hedge α): Id (Rule n (Pred α)) := do
  let mut res := start
  for tree in hedge do
    res := deriv res tree
  return res

-- derive is the derivative function for the expression, given a tree.
-- It returns the expression that is left to match after matching the tree.
-- Note we need to use `partial`, since Lean cannot automatically figure out that the derive function terminates.
-- In OriginalTotal we show how to remove this, by manually proving that it in fact does terminate.
partial def derive [DecidableEq α] (g: Grammar n (Pred α)) (x: Rule n (Pred α)) (tree: Hedge.Node α): Rule n (Pred α) :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol (labelPred, childRef) =>
    -- This is the only rule that differs from regular expressions.
    -- Although if we view this as a complicated predicate, then actually there is no difference.
    if Pred.eval labelPred (Hedge.Node.getLabel tree)
    -- This is exactly the same as: validate childrenExpr (Hedge.Node.getChildren tree)
    && Regex.nullable (List.foldl (derive g) (g.lookup childRef) (Hedge.Node.getChildren tree))
    -- Just like with char, if the predicate matches we return emptystr and if it doesn't we return emptyset
    then Regex.emptystr
    else Regex.emptyset
  | Regex.or y z => Regex.or (derive g y tree) (derive g z tree)
  | Regex.concat y z =>
    if Regex.nullable y
    then Regex.or (Regex.concat (derive g y tree) z) (derive g z tree)
    else Regex.concat (derive g y tree) z
  | Regex.star y => Regex.concat (derive g y tree) (Regex.star y)

partial def validate [DecidableEq α] (g: Grammar n (Pred α)) (x: Rule n (Pred α)) (hedge: Hedge α): Bool :=
  Rule.nullable (List.foldl (derive g) x hedge)

def run [DecidableEq α] (g: Grammar n (Pred α)) (t: Hedge.Node α): Except String Bool :=
  Except.ok (validate g g.start [t])

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
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
  Except.ok true

#guard run
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
  Except.ok true
