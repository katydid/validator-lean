-- ImperativeLeave.lean is an implementation of Leave.lean that does not use monads, so it is more verbose.
-- This is supposed to make it easier to understand for programmers that have not used monads before.

import Validator.Expr.Grammar
import Validator.Expr.Regex

namespace ImperativeLeave

def leave (x: Rule μ α Pred) (ns: List Bool): Except String (Rule μ α Pred × List Bool) :=
  match x with
  | Regex.emptyset => Except.ok (Regex.emptyset, ns)
  | Regex.emptystr => Except.ok (Regex.emptyset, ns)
  | Regex.symbol _ =>
    match ns with
    | [] => Except.error "wtf"
    | (null::ns') =>
      if null
      then Except.ok (Regex.emptystr, ns')
      else Except.ok (Regex.emptyset, ns')
  | Regex.or y z =>
    match leave y ns with
    | Except.error e => Except.error e
    | Except.ok (y', ns') =>
      match leave z ns' with
      | Except.error e => Except.error e
      | Except.ok (z', ns'') =>
        Except.ok (Regex.or y' z', ns'')
  | Regex.concat y z =>
    if Regex.nullable y
    then
      match leave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        match leave z ns' with
        | Except.error e => Except.error e
        | Except.ok (z', ns'') =>
          Except.ok (Regex.or (Regex.concat y' z) z', ns'')
    else
      match leave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        Except.ok (Regex.concat y' z, ns')
  | Regex.star y =>
      match leave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        Except.ok (Regex.star y', ns')

-- deriveLeave takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def deriveLeave (xs: Rules μ α Pred) (ns: List Bool): Except String (Rules μ α Pred) :=
  match xs with
  | [] =>
    match ns with
    | [] => Except.ok []
    | _ => Except.error "Not all nulls were consumed, but there are no expressions to place them in."
  | (x::xs') =>
    let lx': Except String (Rule μ α Pred × List Bool) := leave x ns
    match lx' with
    | Except.error err => Except.error err
    | Except.ok (lx, tailns) =>
    let lxs': Except String (Rules μ α Pred) := deriveLeave xs' tailns
    match lxs' with
    | Except.error err => Except.error err
    | Except.ok lxs =>
      Except.ok (lx::lxs)
