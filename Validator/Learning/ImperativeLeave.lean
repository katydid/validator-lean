-- ImperativeLeave.lean is an implementation of Leave.lean that does not use monads, so it is more verbose.
-- This is supposed to make it easier to understand for programmers that have not used monads before.

import Validator.Expr.Grammar
import Validator.Expr.Regex

namespace ImperativeLeave

def leave (x: Rule μ (Pred α)) (ns: List Bool): (Rule μ (Pred α) × List Bool) :=
  match x with
  | Regex.emptyset => (Regex.emptyset, ns)
  | Regex.emptystr => (Regex.emptyset, ns)
  | Regex.symbol _ =>
    match ns with
    | [] =>
      -- impossible and handled properly with a Vector in non-imperative/proper implementations.
      (x, ns)
    | (null::ns') =>
      if null
      then (Regex.emptystr, ns')
      else (Regex.emptyset, ns')
  | Regex.or y z =>
    let (y', ns') := leave y ns
    let (z', ns'') := leave z ns'
    (Regex.or y' z', ns'')
  | Regex.concat y z =>
    if Regex.nullable y
    then
      let (y', ns') := leave y ns
      let (z', ns'') := leave z ns'
      (Regex.or (Regex.concat y' z) z', ns'')
    else
      let (y', ns') := leave y ns
      (Regex.concat y' z, ns')
  | Regex.star y =>
      let (y', ns') := leave y ns
      (Regex.star y', ns')

-- deriveLeave takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def deriveLeave (xs: List (Rule μ (Pred α))) (ns: List Bool): List (Rule μ (Pred α)) :=
  match xs with
  | [] => []
  | (x::xs') =>
    let (lx, tailns): (Rule μ (Pred α) × List Bool) := leave x ns
    let lxs: List (Rule μ (Pred α)) := deriveLeave xs' tailns
    lx::lxs
