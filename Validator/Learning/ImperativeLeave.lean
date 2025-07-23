-- ImperativeLeave.lean is an implementation of Leave.lean that does not use monads, so it is more verbose.
-- This is supposed to make it easier to understand for programmers that have not used monads before.

import Validator.Expr.Expr

namespace ImperativeLeave

def leave (x: Expr α) (ns: List Bool): Except String (Expr α × List Bool) :=
  match x with
  | Expr.emptyset => Except.ok (Expr.emptyset, ns)
  | Expr.epsilon => Except.ok (Expr.emptyset, ns)
  | Expr.tree _ _ =>
    match ns with
    | [] => Except.error "wtf"
    | (null::ns') =>
      if null
      then Except.ok (Expr.epsilon, ns')
      else Except.ok (Expr.emptyset, ns')
  | Expr.or y z =>
    match leave y ns with
    | Except.error e => Except.error e
    | Except.ok (y', ns') =>
      match leave z ns' with
      | Except.error e => Except.error e
      | Except.ok (z', ns'') =>
        Except.ok (Expr.or y' z', ns'')
  | Expr.concat y z =>
    if Expr.nullable y
    then
      match leave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        match leave z ns' with
        | Except.error e => Except.error e
        | Except.ok (z', ns'') =>
          Except.ok (Expr.or (Expr.concat y' z) z', ns'')
    else
      match leave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        Except.ok (Expr.concat y' z, ns')
  | Expr.star y =>
      match leave y ns with
      | Except.error e => Except.error e
      | Except.ok (y', ns') =>
        Except.ok (Expr.star y', ns')

-- deriveLeave takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def deriveLeave (xs: Exprs α) (ns: List Bool): Except String (Exprs α) :=
  match xs with
  | [] =>
    match ns with
    | [] => Except.ok []
    | _ => Except.error "Not all nulls were consumed, but there are no expressions to place them in."
  | (x::xs') =>
    let lx': Except String (Expr α × List Bool) := leave x ns
    match lx' with
    | Except.error err => Except.error err
    | Except.ok (lx, tailns) =>
    let lxs': Except String (Exprs α) := deriveLeave xs' tailns
    match lxs' with
    | Except.error err => Except.error err
    | Except.ok lxs =>
      Except.ok (lx::lxs)
