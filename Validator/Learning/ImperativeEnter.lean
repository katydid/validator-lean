import Validator.Std.Vec

import Validator.Regex.Regex

namespace ImperativeEnter

def enter (x: Regex σ) (res: List σ := []): List σ :=
  match x with
  | Regex.emptyset => res
  | Regex.emptystr => res
  | Regex.symbol s => s :: res
  | Regex.or y z => enter y (enter z res)
  | Regex.concat y z =>
    if Regex.null y
    then enter y (enter z res)
    else enter y res
  | Regex.star y => enter y res

def deriveEnter (xs: List (Regex σ)): List σ :=
  List.flatten (List.map ImperativeEnter.enter xs)
