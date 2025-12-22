import Std

import Validator.Std.Debug

import Validator.Regex.Regex

import Validator.Regex.Enter

abbrev EnterMem.EnterMap σ [DecidableEq σ] [Hashable σ] :=
  Std.ExtDHashMap
    Nat
    (fun l =>
      Std.ExtDHashMap
        (Vec (Regex σ) l)
        (fun xs =>
          (Vec σ (Symbol.nums xs))
        )
    )

def EnterMem.EnterMap.mk [DecidableEq σ] [Hashable σ] : EnterMap σ := Std.ExtDHashMap.emptyWithCapacity

class EnterMem (m: Type -> Type u) (σ: Type) [DecidableEq σ] [Hashable σ] where
  getEnter : m (EnterMem.EnterMap σ)
  setEnter : (EnterMem.EnterMap σ) → m Unit

namespace EnterMem

def get? [DecidableEq σ] [Hashable σ] (m: EnterMem.EnterMap σ) (xs: Vec (Regex σ) l): Option (Vec σ (Symbol.nums xs)) :=
  match m.get? l with
  | Option.none => Option.none
  | Option.some mxs =>
    match mxs.get? xs with
    | Option.none => Option.none
    | Option.some ifs => Option.some ifs

def insert [DecidableEq σ] [Hashable σ]
  (m: EnterMem.EnterMap σ)
  (key: Vec (Regex σ) l)
  (value: Vec σ (Symbol.nums key))
  : EnterMem.EnterMap σ :=
  match m.get? l with
  | Option.none =>
    m.insert l (Std.ExtDHashMap.emptyWithCapacity.insert key value)
  | Option.some mxs =>
    m.insert l (mxs.insert key value)

def deriveEnter
  [DecidableEq σ] [Hashable σ]
  [Monad m] [Debug m] [EnterMem m σ]
  {l: Nat} (xs: Vec (Regex σ) l): m (Vec σ (Symbol.nums xs)) := do
  let memoized <- EnterMem.getEnter
  match get? memoized xs with
  | Option.none =>
    Debug.debug "cache miss"
    let newvalue := Enter.enters xs
    EnterMem.setEnter (insert memoized xs newvalue)
    return newvalue
  | Option.some value =>
    Debug.debug "cache hit"
    return value

instance [DecidableEq σ] [Hashable σ] [Monad m] [Debug m] [EnterMem m σ] : Enter.DeriveEnter m σ where
  deriveEnter {l: Nat} (xs: Vec (Regex σ) l): m (Vec σ (Symbol.nums xs)) := deriveEnter xs
