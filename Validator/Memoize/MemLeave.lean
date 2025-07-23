import Std

import Validator.Std.Debug

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Leave

namespace MemLeave

abbrev LeaveMap α [DecidableEq α] [Hashable α] := Std.ExtHashMap (Exprs α × List Bool) (Exprs α)
def LeaveMap.mk [DecidableEq α] [Hashable α]: LeaveMap α := Std.ExtHashMap.emptyWithCapacity

class MemLeave (m: Type -> Type u) (α: outParam Type) [DecidableEq α] [Hashable α] where
  getLeave : m (LeaveMap α)
  setLeave : LeaveMap α → m Unit

def deriveLeave
  [DecidableEq α] [Hashable α]
  [Monad m] [Debug m] [MonadExcept String m] [MemLeave m α]
  (xs: Exprs α) (ns: List Bool): m (Exprs α) := do
  let memoized <- MemLeave.getLeave
  match memoized.get? (xs, ns) with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue <- Leave.deriveLeave xs ns
    MemLeave.setLeave (memoized.insert (xs, ns) newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq α] [Hashable α] [Monad m] [Debug m] [MonadExcept String m] [MemLeave m α] : Leave.DeriveLeave m α where
  deriveLeave (xs: Exprs α) (ns: List Bool): m (Exprs α) := deriveLeave xs ns
