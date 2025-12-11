import Std

import Validator.Std.Debug
import Validator.Std.Vec

import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex
import Validator.Expr.Symbol

import Validator.Derive.Leave

def hashRulesAndNulls {n: Nat} {Φ: Type} {l: Nat} [Hashable Φ] (x: (xs: Rules n Φ l) × (Vec Bool (Symbol.nums xs))): UInt64 :=
  mixHash (hash x.1) (hash x.2)

instance (n: Nat) (Φ: Type) (l: Nat) [Hashable Φ] : Hashable ((xs: Rules n Φ l) × (Vec Bool (Symbol.nums xs))) where
  hash := hashRulesAndNulls

abbrev MemLeave.LeaveMap n α [DecidableEq α] [Hashable α] :=
  Std.ExtDHashMap
    Nat
    (fun l =>
      Std.ExtHashMap
        ((xs: Rules n (Pred α) l) × (Vec Bool (Symbol.nums xs)))
        (Rules n (Pred α) l)
    )

def MemLeave.LeaveMap.mk [DecidableEq α] [Hashable α]: LeaveMap n α := Std.ExtDHashMap.emptyWithCapacity

class MemLeave (m: Type -> Type u) (n: outParam Nat) (α: outParam Type) [DecidableEq α] [Hashable α] where
  getLeave : m (MemLeave.LeaveMap n α)
  setLeave : MemLeave.LeaveMap n α → m Unit

namespace MemLeave

def get? [DecidableEq α] [Hashable α]
  (m: MemLeave.LeaveMap n α)
  (key: (xs: Rules n (Pred α) l) × (Vec Bool (Symbol.nums xs)))
  : Option (Rules n (Pred α) l) :=
  match m.get? l with
  | Option.none => Option.none
  | Option.some mkey => mkey.get? key

def insert [DecidableEq α] [Hashable α]
  (m: MemLeave.LeaveMap n α)
  (key: (xs: Rules n (Pred α) l) × (Vec Bool (Symbol.nums xs)))
  (value: Rules n (Pred α) l) :=
  match m.get? l with
  | Option.none =>
    m.insert l (Std.ExtHashMap.emptyWithCapacity.insert key value)
  | Option.some mxs =>
    m.insert l (mxs.insert key value)

def deriveLeaveM
  [DecidableEq α] [Hashable α]
  [Monad m] [Debug m] [MonadExcept String m] [MemLeave m n α]
  (xs: Rules n (Pred α) l) (ns: Vec Bool (Symbol.nums xs)): m (Rules n (Pred α) l) := do
  let memoized <- MemLeave.getLeave
  let key: ((xs: Rules n (Pred α) l) × (Vec Bool (Symbol.nums xs))) := Sigma.mk xs ns
  match get? memoized key with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue := Leave.deriveLeaves xs ns
    MemLeave.setLeave (insert memoized key newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq α] [Hashable α] [Monad m] [Debug m] [MonadExcept String m] [MemLeave m n α] : Leave.DeriveLeaveM m n α where
  deriveLeaveM {l: Nat} (xs: Rules n (Pred α) l) (ns: Vec Bool (Symbol.nums xs)): m (Rules n (Pred α) l) := deriveLeaveM xs ns
