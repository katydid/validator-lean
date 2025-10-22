import Validator.Expr.Grammar
import Validator.Expr.Regex

namespace Leave

def leaveM [Monad m] [MonadExcept String m] (x: Rule μ α Pred) (ns: List Bool): m (Rule μ α Pred × List Bool) := do
  match x with
  | Regex.emptyset => return (Regex.emptyset, ns)
  | Regex.emptystr => return (Regex.emptyset, ns)
  | Regex.symbol _ =>
    match ns with
    | [] =>
      -- Should never occur if ns was acquired from calling `enter`.
      throw "wtf"
    | (null::ns') =>
      if null
      then return (Regex.emptystr, ns')
      else return (Regex.emptyset, ns')
  | Regex.or y z =>
    let (ly, yns) <- leaveM y ns
    let (lz, zns) <- leaveM z yns
    return (Regex.smartOr ly lz, zns)
  | Regex.concat y z =>
    if Regex.nullable y
    then
      let (ly, yns) <- leaveM y ns
      let (lz, zns) <- leaveM z yns
      return (Regex.smartOr (Regex.smartConcat ly z) lz, zns)
    else
      let (ly, yns) <- leaveM y ns
      return (Regex.smartConcat ly z, yns)
  | Regex.star y =>
      let (ly, yns) <- leaveM y ns
      return (Regex.smartConcat ly (Regex.smartStar y), yns)

-- deriveLeaveM takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def deriveLeaveM [Monad m] [MonadExcept String m] (xs: Rules μ α Pred) (ns: List Bool): m (Rules μ α Pred) := do
  match xs with
  | [] =>
    match ns with
    | [] => return []
    | _ => throw "Not all nulls were consumed, but there are no expressions to place them in."
  | (x::xs') =>
    let (lx, tailns) <- leaveM x ns
    let lxs <- deriveLeaveM xs' tailns
    return (lx::lxs)

class DeriveLeaveM (m: Type -> Type u) (μ: Nat) (α: outParam Type) where
  deriveLeaveM (xs: Rules μ α Pred) (ns: List Bool): m (Rules μ α Pred)
