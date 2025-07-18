import Std

import Validator.Std.Debug

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter

namespace MemEnter

abbrev EnterMap := Std.ExtHashMap (List Expr) (List IfExpr)
def EnterMap.mk: EnterMap := Std.ExtHashMap.emptyWithCapacity

class MemEnter (m: Type -> Type u) where
  getEnter : m EnterMap
  setEnter : EnterMap → m Unit

def deriveEnter
  [Monad m] [Debug m] [MemEnter m]
  (xs: List Expr): m (List IfExpr) := do
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

instance [Monad m] [Debug m] [MemEnter m] : Enter.DeriveEnter m where
  deriveEnter (xs: List Expr): m (List IfExpr) := deriveEnter xs
