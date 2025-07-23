import Validator.Expr.Expr

namespace Leave

def leave [Monad m] [MonadExcept String m] (x: Expr α) (ns: List Bool): m (Expr α × List Bool) := do
  match x with
  | Expr.emptyset => return (Expr.emptyset, ns)
  | Expr.epsilon => return (Expr.emptyset, ns)
  | Expr.tree _ _ =>
    match ns with
    | [] => throw "wtf"
    | (null::ns') =>
      if null
      then return (Expr.epsilon, ns')
      else return (Expr.emptyset, ns')
  | Expr.or y z =>
    let (ly, yns) <- leave y ns
    let (lz, zns) <- leave z yns
    return (Expr.smartOr ly lz, zns)
  | Expr.concat y z =>
    if Expr.nullable y
    then
      let (ly, yns) <- leave y ns
      let (lz, zns) <- leave z yns
      return (Expr.smartOr  (Expr.smartConcat ly z) lz, zns)
    else
      let (ly, yns) <- leave y ns
      return (Expr.smartConcat ly z, yns)
  | Expr.star y =>
      let (ly, yns) <- leave y ns
      return (Expr.smartConcat ly (Expr.smartStar y), yns)

-- deriveLeave takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def deriveLeave [Monad m] [MonadExcept String m] (xs: Exprs α) (ns: List Bool): m (Exprs α) := do
  match xs with
  | [] =>
    match ns with
    | [] => return []
    | _ => throw "Not all nulls were consumed, but there are no expressions to place them in."
  | (x::xs') =>
    let (lx, tailns) <- leave x ns
    let lxs <- deriveLeave xs' tailns
    return (lx::lxs)

class DeriveLeave (m: Type -> Type u) (α: outParam Type) where
  deriveLeave (xs: Exprs α) (ns: List Bool): m (Exprs α)
