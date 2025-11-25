import Std

import Validator.Std.Debug

import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex
import Validator.Expr.Symbol

import Validator.Derive.Leave

def hashRulesAndNulls {μ: Nat} {Φ: Type} {ν: Nat} [Hashable Φ] (x: (xs: Rules μ Φ ν) × (List.Vector Bool (Symbol.nums xs))): UInt64 :=
  mixHash (hash x.1) (hash x.2)

instance (μ: Nat) (Φ: Type) (ν: Nat) [Hashable Φ] : Hashable ((xs: Rules μ Φ ν) × (List.Vector Bool (Symbol.nums xs))) where
  hash := hashRulesAndNulls

abbrev MemLeave.LeaveMap μ α [DecidableEq α] [Hashable α] :=
  Std.ExtDHashMap
    Nat
    (fun ν =>
      Std.ExtHashMap
        ((xs: Rules μ (Pred α) ν) × (List.Vector Bool (Symbol.nums xs)))
        (Rules μ (Pred α) ν)
    )

def MemLeave.LeaveMap.mk [DecidableEq α] [Hashable α]: LeaveMap μ α := Std.ExtDHashMap.emptyWithCapacity

class MemLeave (m: Type -> Type u) (μ: outParam Nat) (α: outParam Type) [DecidableEq α] [Hashable α] where
  getLeave : m (MemLeave.LeaveMap μ α)
  setLeave : MemLeave.LeaveMap μ α → m Unit

namespace MemLeave

def get? [DecidableEq α] [Hashable α]
  (m: MemLeave.LeaveMap μ α)
  (key: (xs: Rules μ (Pred α) ν) × (List.Vector Bool (Symbol.nums xs)))
  : Option (Rules μ (Pred α) ν) :=
  match m.get? ν with
  | Option.none => Option.none
  | Option.some mkey => mkey.get? key

def insert [DecidableEq α] [Hashable α]
  (m: MemLeave.LeaveMap μ α)
  (key: (xs: Rules μ (Pred α) ν) × (List.Vector Bool (Symbol.nums xs)))
  (value: Rules μ (Pred α) ν) :=
  match m.get? ν with
  | Option.none =>
    m.insert ν (Std.ExtHashMap.emptyWithCapacity.insert key value)
  | Option.some mxs =>
    m.insert ν (mxs.insert key value)

def deriveLeaveM
  [DecidableEq α] [Hashable α]
  [Monad m] [Debug m] [MonadExcept String m] [MemLeave m μ α]
  (xs: Rules μ (Pred α) ν) (ns: List.Vector Bool (Symbol.nums xs)): m (Rules μ (Pred α) ν) := do
  let memoized <- MemLeave.getLeave
  let key: ((xs: Rules μ (Pred α) ν) × (List.Vector Bool (Symbol.nums xs))) := Sigma.mk xs ns
  match get? memoized key with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue := Leave.deriveLeaves xs ns
    MemLeave.setLeave (insert memoized key newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq α] [Hashable α] [Monad m] [Debug m] [MonadExcept String m] [MemLeave m μ α] : Leave.DeriveLeaveM m μ α where
  deriveLeaveM {ν: Nat} (xs: Rules μ (Pred α) ν) (ns: List.Vector Bool (Symbol.nums xs)): m (Rules μ (Pred α) ν) := deriveLeaveM xs ns
