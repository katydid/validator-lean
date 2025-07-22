import Validator.Capturer.CaptureExpr

namespace CaptureLeave

def leave [Monad m] [MonadExcept String m] (x: CaptureExpr) (ms: List CaptureExpr): m (CaptureExpr × List CaptureExpr) := do
  match x with
  | CaptureExpr.emptyset => return (CaptureExpr.emptyset, ms)
  | CaptureExpr.epsilon => return (CaptureExpr.emptyset, ms)
  -- matched acts the same as epsilon.
  | CaptureExpr.matched _ _ => return (CaptureExpr.emptyset, ms)
  | CaptureExpr.tree _ _ =>
    match ms with
    | [] => throw "wtf"
    | (m'::ms') => return (m', ms')
  | CaptureExpr.or y z =>
    let (ly, yms) <- leave y ms
    let (lz, zms) <- leave z yms
    return (CaptureExpr.smartOr ly lz, zms)
  | CaptureExpr.concat y z =>
    if CaptureExpr.nullable y
    then
      let (ly, yms) <- leave y ms
      let (lz, zms) <- leave z yms
      let dx := CaptureExpr.smartOr
        (CaptureExpr.smartConcat ly z)
        -- Specifically for capturing: instead of lz, we write:
        (CaptureExpr.smartConcat (CaptureExpr.neutralize y) lz)
      return (dx, zms)
    else
      let (ly, yms) <- leave y ms
      return (CaptureExpr.smartConcat ly z, yms)
  | CaptureExpr.star y =>
    let (ly, yms) <- leave y ms
    return (CaptureExpr.smartConcat ly (CaptureExpr.smartStar y), yms)
  | CaptureExpr.group id y =>
    let (ly, yms) <- leave y ms
    return (CaptureExpr.smartGroup id ly, yms)

-- deriveLeave takes a list of expressions and list of bools.
-- The list of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each tree expression with either an epsilon or emptyset.
-- The lists do not to be the same length, because each expression can contain an arbitrary number of tree expressions.
def deriveLeave [Monad m] [MonadExcept String m] (xs: List CaptureExpr) (ms: List CaptureExpr): m (List CaptureExpr) := do
  match xs with
  | [] =>
    match ms with
    | [] => return []
    | _ => throw "Not all matches were consumed, but there are no expressions to place them in."
  | (x::xs') =>
    let (lx, tailms) <- leave x ms
    let lxs <- deriveLeave xs' tailms
    return (lx::lxs)

class DeriveLeave (m: Type -> Type u) where
  deriveLeave (xs: List CaptureExpr) (ns: List Bool): m (List CaptureExpr)
