import Validator.Std.Linter.DetectClassical

import Validator.Expr.Expr

namespace Leave

def leaveM [Monad m] [MonadExcept String m] (x: Expr α) (ns: List Bool): m (Expr α × List Bool) := do
  match x with
  | Expr.emptyset => return (Expr.emptyset, ns)
  | Expr.epsilon => return (Expr.emptyset, ns)
  | Expr.tree _ _ =>
    match ns with
    | [] =>
      -- Should never occur if ns was acquired from calling `enter`.
      throw "wtf"
    | (null::ns') =>
      if null
      then return (Expr.epsilon, ns')
      else return (Expr.emptyset, ns')
  | Expr.or y z =>
    let (ly, yns) <- leaveM y ns
    let (lz, zns) <- leaveM z yns
    return (Expr.smartOr ly lz, zns)
  | Expr.concat y z =>
    if Expr.nullable y
    then
      let (ly, yns) <- leaveM y ns
      let (lz, zns) <- leaveM z yns
      return (Expr.smartOr (Expr.smartConcat ly z) lz, zns)
    else
      let (ly, yns) <- leaveM y ns
      return (Expr.smartConcat ly z, yns)
  | Expr.star y =>
      let (ly, yns) <- leaveM y ns
      return (Expr.smartConcat ly (Expr.smartStar y), yns)

-- deriveLeaveM takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def deriveLeaveM [Monad m] [MonadExcept String m] (xs: Exprs α) (ns: List Bool): m (Exprs α) := do
  match xs with
  | [] =>
    match ns with
    | [] => return []
    | _ => throw "Not all nulls were consumed, but there are no expressions to place them in."
  | (x::xs') =>
    let (lx, tailns) <- leaveM x ns
    let lxs <- deriveLeaveM xs' tailns
    return (lx::lxs)

class DeriveLeaveM (m: Type -> Type u) (α: outParam Type) where
  deriveLeaveM (xs: Exprs α) (ns: List Bool): m (Exprs α)
