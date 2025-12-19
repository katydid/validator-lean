import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr
import Validator.Regex.Symbol

namespace ImperativeEnter

def enter (x: Rule n φ) (res: List (IfExpr n φ) := []): List (IfExpr n φ) :=
  match x with
  | Regex.emptyset => res
  | Regex.emptystr => res
  | Regex.symbol s => s :: res
  | Regex.or y z => enter y (enter z res)
  | Regex.concat y z =>
    if Regex.nullable y
    then enter y (enter z res)
    else enter y res
  | Regex.star y => enter y res

def deriveEnter (xs: List (Rule n φ)): List (IfExpr n φ) :=
  List.flatten (List.map ImperativeEnter.enter xs)
