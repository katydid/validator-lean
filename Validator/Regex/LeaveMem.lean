import Std

import Validator.Std.Debug
import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Regex.Symbol
import Validator.Regex.LeaveSmart

def hashRulesAndNulls {l: Nat} [Hashable σ] (x: (xs: Vec (Regex σ) l) × (Vec Bool (Symbol.nums xs))): UInt64 :=
  mixHash (hash x.1) (hash x.2)

instance (σ: Type) (l: Nat) [Hashable σ] : Hashable ((xs: Vec (Regex σ) l) × (Vec Bool (Symbol.nums xs))) where
  hash := hashRulesAndNulls

abbrev LeaveMem.LeaveMap σ [DecidableEq σ] [Hashable σ] :=
  Std.ExtDHashMap
    Nat
    (fun l =>
      Std.ExtHashMap
        ((xs: Vec (Regex σ) l) × (Vec Bool (Symbol.nums xs)))
        (Vec (Regex σ) l)
    )

def LeaveMem.LeaveMap.mk [DecidableEq σ] [Hashable σ]: LeaveMap σ := Std.ExtDHashMap.emptyWithCapacity

class LeaveMem (m: Type -> Type u) (σ: Type) [DecidableEq σ] [Hashable σ] where
  getLeave : m (LeaveMem.LeaveMap σ)
  setLeave : LeaveMem.LeaveMap σ → m Unit

namespace LeaveMem

def get? [DecidableEq σ] [Hashable σ]
  (m: LeaveMem.LeaveMap σ)
  (key: (xs: Vec (Regex σ) l) × (Vec Bool (Symbol.nums xs)))
  : Option (Vec (Regex σ) l) :=
  match m.get? l with
  | Option.none => Option.none
  | Option.some mkey => mkey.get? key

def insert [DecidableEq σ] [Hashable σ]
  (m: LeaveMem.LeaveMap σ)
  (key: (xs: Vec (Regex σ) l) × (Vec Bool (Symbol.nums xs)))
  (value: Vec (Regex σ) l) :=
  match m.get? l with
  | Option.none =>
    m.insert l (Std.ExtHashMap.emptyWithCapacity.insert key value)
  | Option.some mxs =>
    m.insert l (mxs.insert key value)

def deriveLeaveM
  [DecidableEq σ] [Hashable σ]
  [Monad m] [Debug m] [MonadExcept String m] [LeaveMem m σ]
  (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l) := do
  let memoized <- LeaveMem.getLeave
  let key: ((xs: Vec (Regex σ) l) × (Vec Bool (Symbol.nums xs))) := Sigma.mk xs ns
  match get? memoized key with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue := LeaveSmart.deriveLeaves xs ns
    LeaveMem.setLeave (insert memoized key newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq σ] [Hashable σ] [Monad m] [Debug m] [MonadExcept String m] [LeaveMem m σ] : LeaveSmart.DeriveLeaveM m σ where
  deriveLeaveM {l: Nat} (xs: Vec (Regex σ) l) (ns: Vec Bool (Symbol.nums xs)): m (Vec (Regex σ) l) := deriveLeaveM xs ns
