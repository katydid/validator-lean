import Mathlib.Data.Vector.Snoc

import Validator.Expr.Regex
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Symbol

namespace ImperativeEnter

def enter (x: Rule n (Pred α)) (res: List (IfExpr n α) := []): List (IfExpr n α) :=
  match x with
  | Regex.emptyset => res
  | Regex.emptystr => res
  | Regex.symbol (pred, childRef) => (IfExpr.mk pred childRef) :: res
  | Regex.or y z => enter y (enter z res)
  | Regex.concat y z =>
    if Regex.nullable y
    then enter y (enter z res)
    else enter y res
  | Regex.star y => enter y res

def deriveEnter (xs: List (Rule n (Pred α))): List (IfExpr n α) :=
    List.flatten (List.map ImperativeEnter.enter xs)
