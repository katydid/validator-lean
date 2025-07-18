import Validator.Expr.Expr
import Validator.Expr.Smart

namespace Leave

def leave [Monad m] [MonadExcept String m] (x: Expr) (ns: List Bool): m (Expr × List Bool) := do
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
    return (Smart.or ly lz, zns)
  | Expr.concat y z =>
    if Expr.nullable y
    then
      let (ly, yns) <- leave y ns
      let (lz, zns) <- leave z yns
      return (Smart.or (Smart.concat ly z) lz, zns)
    else
      let (ly, yns) <- leave y ns
      return (Smart.concat ly z, yns)
  | Expr.star y =>
      let (ly, yns) <- leave y ns
      return (Smart.star ly, yns)

-- leaves takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def leaves [Monad m] [MonadExcept String m] (xs: List Expr) (ns: List Bool): m (List Expr) := do
  match xs with
  | [] =>
    match ns with
    | [] => return []
    | _ => throw "Not all nulls were consumed, but there are no expressions to place them in."
  | (x::xs') =>
    let (lx, tailns) <- leave x ns
    let lxs <- leaves xs' tailns
    return (lx::lxs)

class DeriveLeaves (m: Type -> Type u) where
  deriveLeaves (xs: List Expr) (ns: List Bool): m (List Expr)

instance : DeriveLeaves (Except String) where
  deriveLeaves := leaves
