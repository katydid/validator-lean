-- Original is the original derivative algorithm that runs on a labelled tree.
-- It is intended to be used for explanation purposes.
-- This version cannot be memoized effectively, but it is the easiest version to understand.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Pred
import Validator.Expr.Expr

namespace Original

-- foldLoop is a more readable version of List.foldl for imperative programmers:
-- Imperative programmers can imagine that `Id (Expr α)` = `Expr α`, because it does.
-- The Id wrapper just adds a monad wrapper to enable the do notation, so that we can use the for loop in Lean.
private def foldLoop (deriv: Expr μ α -> Hedge.Node α -> Expr μ α) (start: Expr μ α) (hedge: Hedge α): Id (Expr μ α) := do
  let mut res := start
  for tree in hedge do
    res := deriv res tree
  return res

-- derive is the derivative function for the expression, given a tree.
-- It returns the expression that is left to match after matching the tree.
-- Note we need to use `partial`, since Lean cannot automatically figure out that the derive function terminates.
-- In OriginalTotal we show how to remove this, by manually proving that it in fact does terminate.
partial def derive [DecidableEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (tree: Hedge.Node α): Expr μ α :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childRef =>
    -- This is the only rule that differs from regular expressions.
    -- Although if we view this as a complicated predicate, then actually there is no difference.
    if Pred.eval labelPred (Hedge.Node.getLabel tree)
    -- This is exactly the same as: validate childrenExpr (Hedge.Node.getChildren tree)
    && Expr.nullable (List.foldl (derive g) (g.lookup childRef) (Hedge.Node.getChildren tree))
    -- Just like with char, if the predicate matches we return epsilon and if it doesn't we return emptyset
    then Expr.epsilon
    else Expr.emptyset
  | Expr.or y z => Expr.or (derive g y tree) (derive g z tree)
  | Expr.concat y z =>
    if Expr.nullable y
    then Expr.or (Expr.concat (derive g y tree) z) (derive g z tree)
    else Expr.concat (derive g y tree) z
  | Expr.star y => Expr.concat (derive g y tree) (Expr.star y)

partial def validate [DecidableEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (hedge: Hedge α): Bool :=
  Expr.nullable (List.foldl (derive g) x hedge)

def run [DecidableEq α] (g: Expr.Grammar μ α) (t: Hedge.Node α): Except String Bool :=
  Except.ok (validate g g.lookup0 [t])

-- Tests
-- Lean can use #guard to run these tests at compile time.

open TokenTree (node)

#guard run
  (Expr.Grammar.singleton Expr.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.tree (Pred.eq (Token.string "b")) 2)
      , Expr.epsilon
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
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
  Except.ok true

#guard run
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
  Except.ok true
