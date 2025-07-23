import Std

import Validator.Std.Debug

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter

namespace MemEnter

abbrev EnterMap α [DecidableEq α] [Hashable α] := Std.ExtHashMap (Exprs α) (IfExprs α)
def EnterMap.mk [DecidableEq α] [Hashable α] : EnterMap α := Std.ExtHashMap.emptyWithCapacity

class MemEnter (m: Type -> Type u) (α: outParam Type) [DecidableEq α] [Hashable α] where
  getEnter : m (EnterMap α)
  setEnter : (EnterMap α) → m Unit

def deriveEnter
  [DecidableEq α] [Hashable α]
  [Monad m] [Debug m] [MemEnter m α]
  (xs: Exprs α): m (IfExprs α) := do
  let memoized <- MemEnter.getEnter
  match memoized.get? xs with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue := Enter.deriveEnter xs
    MemEnter.setEnter (memoized.insert xs newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq α] [Hashable α] [Monad m] [Debug m] [MemEnter m α] : Enter.DeriveEnter m α where
  deriveEnter (xs: Exprs α): m (IfExprs α) := deriveEnter xs
