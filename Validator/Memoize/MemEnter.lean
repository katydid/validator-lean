import Std

import Validator.Std.Debug

import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr
import Validator.Regex.Regex
import Validator.Regex.Symbol

import Validator.Derive.Enter

abbrev MemEnter.EnterMap (n: Nat) φ [DecidableEq φ] [Hashable φ] :=
  Std.ExtDHashMap
    Nat
    (fun l =>
      Std.ExtDHashMap
        (Rules n φ l)
        (fun xs =>
          (IfExprs n φ (Symbol.nums xs))
        )
    )

def MemEnter.EnterMap.mk [DecidableEq φ] [Hashable φ] : EnterMap n φ := Std.ExtDHashMap.emptyWithCapacity

class MemEnter (m: Type -> Type u) (n: Nat) (φ: Type) [DecidableEq φ] [Hashable φ] where
  getEnter : m (MemEnter.EnterMap n φ)
  setEnter : (MemEnter.EnterMap n φ) → m Unit

namespace MemEnter

def get? [DecidableEq φ] [Hashable φ] (m: MemEnter.EnterMap n φ) (xs: Rules n φ l): Option (IfExprs n φ (Symbol.nums xs)) :=
  match m.get? l with
  | Option.none => Option.none
  | Option.some mxs =>
    match mxs.get? xs with
    | Option.none => Option.none
    | Option.some ifs => Option.some ifs

def insert [DecidableEq φ] [Hashable φ]
  (m: MemEnter.EnterMap n φ)
  (key: Rules n φ l)
  (value: IfExprs n φ (Symbol.nums key))
  : MemEnter.EnterMap n φ :=
  match m.get? l with
  | Option.none =>
    m.insert l (Std.ExtDHashMap.emptyWithCapacity.insert key value)
  | Option.some mxs =>
    m.insert l (mxs.insert key value)

def deriveEnter
  [DecidableEq φ] [Hashable φ]
  [Monad m] [Debug m] [MemEnter m n φ]
  {l: Nat} (xs: Rules n φ l): m (IfExprs n φ (Symbol.nums xs)) := do
  let memoized <- MemEnter.getEnter
  match get? memoized xs with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue := Enter.deriveEnter xs
    MemEnter.setEnter (insert memoized xs newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq φ] [Hashable φ] [Monad m] [Debug m] [MemEnter m n φ] : Enter.DeriveEnter m n φ where
  deriveEnter {l: Nat} (xs: Rules n φ l): m (IfExprs n φ (Symbol.nums xs)) := deriveEnter xs
