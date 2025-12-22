import Std

import Validator.Std.Debug
import Validator.Std.Vec

import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr
import Validator.Regex.Regex
import Validator.Regex.Symbol

import Validator.Regex.LeaveSmart

def hashRulesAndNulls {n: Nat} {φ: Type} {l: Nat} [Hashable φ] (x: (xs: Rules n φ l) × (Vec Bool (Symbol.nums xs))): UInt64 :=
  mixHash (hash x.1) (hash x.2)

instance (n: Nat) (φ: Type) (l: Nat) [Hashable φ] : Hashable ((xs: Rules n φ l) × (Vec Bool (Symbol.nums xs))) where
  hash := hashRulesAndNulls

abbrev MemLeave.LeaveMap n φ [DecidableEq φ] [Hashable φ] :=
  Std.ExtDHashMap
    Nat
    (fun l =>
      Std.ExtHashMap
        ((xs: Rules n φ l) × (Vec Bool (Symbol.nums xs)))
        (Rules n φ l)
    )

def MemLeave.LeaveMap.mk [DecidableEq α] [Hashable α]: LeaveMap n α := Std.ExtDHashMap.emptyWithCapacity

class MemLeave (m: Type -> Type u) (n: Nat) (φ: Type) [DecidableEq φ] [Hashable φ] where
  getLeave : m (MemLeave.LeaveMap n φ)
  setLeave : MemLeave.LeaveMap n φ → m Unit

namespace MemLeave

def get? [DecidableEq φ] [Hashable φ]
  (m: MemLeave.LeaveMap n φ)
  (key: (xs: Rules n φ l) × (Vec Bool (Symbol.nums xs)))
  : Option (Rules n φ l) :=
  match m.get? l with
  | Option.none => Option.none
  | Option.some mkey => mkey.get? key

def insert [DecidableEq φ] [Hashable φ]
  (m: MemLeave.LeaveMap n φ)
  (key: (xs: Rules n φ l) × (Vec Bool (Symbol.nums xs)))
  (value: Rules n φ l) :=
  match m.get? l with
  | Option.none =>
    m.insert l (Std.ExtHashMap.emptyWithCapacity.insert key value)
  | Option.some mxs =>
    m.insert l (mxs.insert key value)

def deriveLeaveM
  [DecidableEq φ] [Hashable φ]
  [Monad m] [Debug m] [MonadExcept String m] [MemLeave m n φ]
  (xs: Rules n φ l) (ns: Vec Bool (Symbol.nums xs)): m (Rules n φ l) := do
  let memoized <- MemLeave.getLeave
  let key: ((xs: Rules n φ l) × (Vec Bool (Symbol.nums xs))) := Sigma.mk xs ns
  match get? memoized key with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue := LeaveSmart.deriveLeaves xs ns
    MemLeave.setLeave (insert memoized key newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq φ] [Hashable φ] [Monad m] [Debug m] [MonadExcept String m] [MemLeave m n φ] : LeaveSmart.DeriveLeaveM m (Symbol n φ) where
  deriveLeaveM {l: Nat} (xs: Rules n φ l) (ns: Vec Bool (Symbol.nums xs)): m (Rules n φ l) := deriveLeaveM xs ns
