import Std

import Validator.Std.Debug

import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex
import Validator.Expr.Symbol

import Validator.Derive.Enter

abbrev MemEnter.EnterMap (n: Nat) α [DecidableEq α] [Hashable α] :=
  Std.ExtDHashMap
    Nat
    (fun l =>
      Std.ExtDHashMap
        (Rules n (Pred α) l)
        (fun xs =>
          (IfExprs n α (Symbol.nums xs))
        )
    )

def MemEnter.EnterMap.mk [DecidableEq α] [Hashable α] : EnterMap n α := Std.ExtDHashMap.emptyWithCapacity

class MemEnter (m: Type -> Type u) (n: outParam Nat) (α: outParam Type) [DecidableEq α] [Hashable α] where
  getEnter : m (MemEnter.EnterMap n α)
  setEnter : (MemEnter.EnterMap n α) → m Unit

namespace MemEnter

def get? [DecidableEq α] [Hashable α] (m: MemEnter.EnterMap n α) (xs: Rules n (Pred α) l): Option (IfExprs n α (Symbol.nums xs)) :=
  match m.get? l with
  | Option.none => Option.none
  | Option.some mxs =>
    match mxs.get? xs with
    | Option.none => Option.none
    | Option.some ifs => Option.some ifs

def insert [DecidableEq α] [Hashable α]
  (m: MemEnter.EnterMap n α)
  (key: Rules n (Pred α) l)
  (value: IfExprs n α (Symbol.nums key))
  : MemEnter.EnterMap n α :=
  match m.get? l with
  | Option.none =>
    m.insert l (Std.ExtDHashMap.emptyWithCapacity.insert key value)
  | Option.some mxs =>
    m.insert l (mxs.insert key value)

def deriveEnter
  [DecidableEq α] [Hashable α]
  [Monad m] [Debug m] [MemEnter m n α]
  {l: Nat} (xs: Rules n (Pred α) l): m (IfExprs n α (Symbol.nums xs)) := do
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

instance [DecidableEq α] [Hashable α] [Monad m] [Debug m] [MemEnter m n α] : Enter.DeriveEnter m n α where
  deriveEnter {l: Nat} (xs: Rules n (Pred α) l): m (IfExprs n α (Symbol.nums xs)) := deriveEnter xs
