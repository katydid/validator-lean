import Std

import Validator.Std.Debug

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter

abbrev MemEnter.EnterMap (μ: Nat) α [DecidableEq α] [Hashable α] := Std.ExtHashMap (Exprs μ α) (IfExprs μ α)
def MemEnter.EnterMap.mk [DecidableEq α] [Hashable α] : EnterMap μ α := Std.ExtHashMap.emptyWithCapacity

class MemEnter (m: Type -> Type u) (μ: outParam Nat) (α: outParam Type) [DecidableEq α] [Hashable α] where
  getEnter : m (MemEnter.EnterMap μ α)
  setEnter : (MemEnter.EnterMap μ α) → m Unit

namespace MemEnter

def deriveEnter
  [DecidableEq α] [Hashable α]
  [Monad m] [Debug m] [MemEnter m μ α]
  (xs: Exprs μ α): m (IfExprs μ α) := do
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

instance [DecidableEq α] [Hashable α] [Monad m] [Debug m] [MemEnter m μ α] : Enter.DeriveEnter m μ α where
  deriveEnter (xs: Exprs μ α): m (IfExprs μ α) := deriveEnter xs
