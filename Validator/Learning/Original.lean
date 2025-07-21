-- Original is the original derivative algorithm that runs on a labelled tree.
-- It is intended to be used for explanation purposes.
-- This version cannot be memoized effectively, but it is the easiest version to understand.

import Validator.Std.Except

import Validator.Parser.ParseTree

import Validator.Expr.Pred
import Validator.Expr.Expr

namespace Original

-- foldLoop is a more readable version of List.foldl for imperative programmers:
-- TODO: explain to ignore Id
private def foldLoop (deriv: Expr -> ParseTree -> Expr) (start: Expr) (forest: List ParseTree): Id Expr := do
  let mut res := start
  for tree in forest do
    res := deriv res tree
  return res

-- TODO: explain to ignore partial or try to rewrite this to be easier for termination checker to see this is terminating.
partial def derive (x: Expr) (tree: ParseTree): Expr :=
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

partial def validate (x: Expr) (forest: List ParseTree): Bool :=
  Expr.nullable (List.foldl derive x forest)

def run (x: Expr) (t: ParseTree): Except String Bool :=
  Except.ok (validate x [t])

-- Tests
-- Lean can use #guard to run these tests at compile time.

open ParseTree (node)

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
