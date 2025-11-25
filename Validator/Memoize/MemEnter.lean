import Std

import Validator.Std.Debug

import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex
import Validator.Expr.Symbol

import Validator.Derive.Enter

abbrev MemEnter.EnterMap (μ: Nat) α [DecidableEq α] [Hashable α] :=
  Std.ExtDHashMap
    Nat
    (fun ν =>
      Std.ExtDHashMap
        (Rules μ (Pred α) ν)
        (fun xs =>
          (IfExprs μ α (Symbol.nums xs))
        )
    )

def MemEnter.EnterMap.mk [DecidableEq α] [Hashable α] : EnterMap μ α := Std.ExtDHashMap.emptyWithCapacity

class MemEnter (m: Type -> Type u) (μ: outParam Nat) (α: outParam Type) [DecidableEq α] [Hashable α] where
  getEnter : m (MemEnter.EnterMap μ α)
  setEnter : (MemEnter.EnterMap μ α) → m Unit

namespace MemEnter

def get? [DecidableEq α] [Hashable α] (m: MemEnter.EnterMap μ α) (xs: Rules μ (Pred α) ν): Option (IfExprs μ α (Symbol.nums xs)) :=
  match m.get? ν with
  | Option.none => Option.none
  | Option.some mxs =>
    match mxs.get? xs with
    | Option.none => Option.none
    | Option.some ifs => Option.some ifs

def insert [DecidableEq α] [Hashable α]
  (m: MemEnter.EnterMap μ α)
  (key: Rules μ (Pred α) ν)
  (value: IfExprs μ α (Symbol.nums key))
  : MemEnter.EnterMap μ α :=
  match m.get? ν with
  | Option.none =>
    m.insert ν (Std.ExtDHashMap.emptyWithCapacity.insert key value)
  | Option.some mxs =>
    m.insert ν (mxs.insert key value)

def deriveEnter
  [DecidableEq α] [Hashable α]
  [Monad m] [Debug m] [MemEnter m μ α]
  {ν: Nat} (xs: Rules μ (Pred α) ν): m (IfExprs μ α (Symbol.nums xs)) := do
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

instance [DecidableEq α] [Hashable α] [Monad m] [Debug m] [MemEnter m μ α] : Enter.DeriveEnter m μ α where
  deriveEnter {ν: Nat} (xs: Rules μ (Pred α) ν): m (IfExprs μ α (Symbol.nums xs)) := deriveEnter xs
