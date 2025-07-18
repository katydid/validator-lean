-- Original is the original derivative algorithm that runs on a labelled tree.
-- It is intended to be used for explanation purposes.
-- This version cannot be memoized effectively, but it is the easiest version to understand.

import Validator.Parser.ParseTree

import Validator.Expr.Pred
import Validator.Expr.Expr

namespace Original

-- foldLoop is a more readable version of List.foldl for imperative programmers:
private def foldLoop (deriv: Expr -> ParseTree -> Expr) (start: Expr) (forest: List ParseTree): Id Expr := do
  let mut res := start
  for tree in forest do
    res := deriv res tree
  return res

partial def derive (x: Expr) (t: ParseTree): Expr :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childrenExpr =>
    -- This is the only rule that differs from regular expressions.
    -- Although if we view this as a complicated predicate, then actually there is no difference.
    if Pred.eval labelPred (ParseTree.getLabel t)
    && Expr.nullable (List.foldl derive childrenExpr (ParseTree.getChildren t))
    then Expr.epsilon
    else Expr.emptyset
  | Expr.or y z => Expr.or (derive y t) (derive z t)
  | Expr.concat y z =>
    if Expr.nullable y
    then Expr.or (Expr.concat (derive y t) z) (derive z t)
    else Expr.concat (derive y t) z
  | Expr.star y => Expr.concat (derive y t) (Expr.star y)

partial def validate (x: Expr) (forest: List ParseTree): Bool :=
  Expr.nullable (List.foldl derive x forest)

def run (x: Expr) (t: ParseTree): Except String Bool :=
  Except.ok (validate x [t])

-- Tests
-- Lean can use #guard to run these tests at compile time.

open ParseTree (field)

#guard run
  Expr.emptyset
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (field "a" [field "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (field "a" [field "b" []]) =
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
  (field "a" [field "b" [], field "c" []]) =
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
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok true
