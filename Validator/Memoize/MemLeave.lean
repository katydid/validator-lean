import Std

import Validator.Std.Debug

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Leave

abbrev MemLeave.LeaveMap μ α [DecidableEq α] [Hashable α] := Std.ExtHashMap (Exprs μ α × List Bool) (Exprs μ α)
def MemLeave.LeaveMap.mk [DecidableEq α] [Hashable α]: LeaveMap μ α := Std.ExtHashMap.emptyWithCapacity

class MemLeave (m: Type -> Type u) (μ: outParam Nat) (α: outParam Type) [DecidableEq α] [Hashable α] where
  getLeave : m (MemLeave.LeaveMap μ α)
  setLeave : MemLeave.LeaveMap μ α → m Unit

namespace MemLeave

def deriveLeaveM
  [DecidableEq α] [Hashable α]
  [Monad m] [Debug m] [MonadExcept String m] [MemLeave m μ α]
  (xs: Exprs μ α) (ns: List Bool): m (Exprs μ α) := do
  let memoized <- MemLeave.getLeave
  match memoized.get? (xs, ns) with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue <- Leave.deriveLeaveM xs ns
    MemLeave.setLeave (memoized.insert (xs, ns) newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq α] [Hashable α] [Monad m] [Debug m] [MonadExcept String m] [MemLeave m μ α] : Leave.DeriveLeaveM m μ α where
  deriveLeaveM (xs: Exprs μ α) (ns: List Bool): m (Exprs μ α) := deriveLeaveM xs ns
