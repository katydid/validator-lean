import Validator.Expr.Expr

namespace Leave

def leave (x: Expr) (ns: List Bool): Except String (Expr × List Bool) :=
  match x with
  | Expr.emptyset => Except.ok (Expr.emptyset, ns)
  | Expr.epsilon => Except.ok (Expr.epsilon, ns)
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

-- leaves takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def leaves (xs: List Expr) (ns: List Bool): Except String (List Expr) :=
  match xs with
  | [] =>
    match ns with
    | [] => Except.ok []
    | _ => Except.error "nulls are left, but there are no expressions to place them in"
  | (x::xs') =>
    let dl: Except String (Expr × List Bool) := leave x ns
    match dl with
    | Except.error err => Except.error err
    | Except.ok (dx, tailns) =>
      let dls: Except String (List Expr) := leaves xs' tailns
      match dls with
      | Except.error err => Except.error err
      | Except.ok dxs' =>
        Except.ok (dx::dxs')
