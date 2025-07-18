import Std

import Validator.Std.Debug

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Leave

namespace MemLeave

abbrev LeaveMap := Std.ExtHashMap (List Expr × List Bool) (List Expr)
def LeaveMap.mk: LeaveMap := Std.ExtHashMap.emptyWithCapacity

class MemLeave (m: Type -> Type u) where
  getLeave : m LeaveMap
  setLeave : LeaveMap → m Unit

instance [Monad m] [MonadStateOf LeaveMap m] : MemLeave m where
  getLeave := MonadStateOf.get
  setLeave s := MonadStateOf.set s

def deriveLeave
  [Monad m] [Debug m] [MonadExcept String m] [MemLeave m]
  (xs: List Expr) (ns: List Bool): m (List Expr) := do
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

instance [Monad m] [Debug m] [MonadExcept String m] [MemLeave m] : Leave.DeriveLeave m where
  deriveLeave (xs: List Expr) (ns: List Bool): m (List Expr) := deriveLeave xs ns
