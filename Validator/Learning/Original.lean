-- Original is the original derivative algorithm that runs on a labelled tree.
-- It is intended to be used for explanation purposes.
-- This version cannot be memoized effectively, but it is the easiest version to understand.

import Validator.Std.Except

import Validator.Std.ParseTree
import Validator.Parser.TokenTree

import Validator.Expr.Pred
import Validator.Expr.Expr

namespace Original

-- foldLoop is a more readable version of List.foldl for imperative programmers:
-- Imperative programmers can imagine that `Id (Expr α)` = `Expr α`, because it does.
-- The Id wrapper just adds a monad wrapper to enable the do notation, so that we can use the for loop in Lean.
private def foldLoop (deriv: Expr α -> ParseTree α -> Expr α) (start: Expr α) (forest: ParseForest α): Id (Expr α) := do
  let mut res := start
  for tree in forest do
    res := deriv res tree
  return res

-- derive is the derivative function for the expression, given a tree.
-- It returns the expression that is left to match after matching the tree.
-- Note we need to use `partial`, since Lean cannot automatically figure out that the derive function terminates.
-- In OriginalTotal we show how to remove this, by manually proving that it in fact does terminate.
partial def derive [DecidableEq α] (x: Expr α) (tree: ParseTree α): Expr α :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childrenExpr =>
    -- This is the only rule that differs from regular expressions.
    -- Although if we view this as a complicated predicate, then actually there is no difference.
    if Pred.eval labelPred (ParseTree.getLabel tree)
    -- This is exactly the same as: validate childrenExpr (ParseTree.getChildren tree)
    && Expr.nullable (List.foldl derive childrenExpr (ParseTree.getChildren tree))
    -- Just like with char, if the predicate matches we return epsilon and if it doesn't we return emptyset
    then Expr.epsilon
    else Expr.emptyset
  | Expr.or y z => Expr.or (derive y tree) (derive z tree)
  | Expr.concat y z =>
    if Expr.nullable y
    then Expr.or (Expr.concat (derive y tree) z) (derive z tree)
    else Expr.concat (derive y tree) z
  | Expr.star y => Expr.concat (derive y tree) (Expr.star y)

partial def validate [DecidableEq α] (x: Expr α) (forest: ParseForest α): Bool :=
  Expr.nullable (List.foldl derive x forest)

def run [DecidableEq α] (x: Expr α) (t: ParseTree α): Except String Bool :=
  Except.ok (validate x [t])

-- Tests
-- Lean can use #guard to run these tests at compile time.

open TokenTree (node)

#guard run
  Expr.emptyset
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (node "a" [node "b" []]) =
  Except.ok true

#guard run
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

#guard run
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
