-- LTreeOriginal is the original derivative algorithm that runs on a labelled tree.
-- It is intended to be used for explanation purposes.
-- This version cannot be memoized effectively, but it is the easiest version to understand.

import Validator.Expr.Expr

namespace LTreeOriginal

partial def derive (x: Expr) (t: LTree): Expr :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childrenExpr =>
    let childResExpr := List.foldl derive childrenExpr (LTree.children t)
    if labelPred (Token.string (LTree.label t))
    then
      if Expr.nullable childResExpr
      then Expr.epsilon
      else Expr.emptyset
    else Expr.emptyset
  | Expr.or y z => Expr.or (derive y t) (derive z t)
  | Expr.concat y z =>
    if Expr.nullable y
    then Expr.or (Expr.concat (derive y t) z) (derive z t)
    else Expr.concat (derive y t) z
  | Expr.star y => Expr.concat (derive y t) (Expr.star y)

partial def validate (x: Expr) (forest: List LTree): Bool :=
  Expr.nullable (List.foldl derive x forest)
