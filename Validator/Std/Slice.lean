import Validator.Std.List
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.RewriteSearch

structure SliceOf (data: List α) where
  offset: Nat
  len: Nat
  prop: offset + len <= data.length

def SliceOf.isEmpty {xs: List α} (s: SliceOf xs): Bool :=
  s.len = 0

def SliceOf.mk' (init: List α): SliceOf init :=
  SliceOf.mk 0 init.length (by simp only [zero_add, le_refl])

def SliceOf.length (s: SliceOf xs): Nat :=
  s.len

def SliceOf.nonEmpty {α: Type} {xs: List α} (s: SliceOf xs): Option {ys: SliceOf xs // ys.length > 0} :=
  match h: s.len with
  | 0 => Option.none
  | l + 1 => Option.some (Subtype.mk s (by
    simp [SliceOf.length]
    omega
  ))

def SliceOf.val {xs: List α} (s: SliceOf xs): List α :=
  List.take s.len (List.drop s.offset xs)

def SliceOf.take {xs: List α} (n: Nat) (s: SliceOf xs): SliceOf xs :=
  SliceOf.mk s.offset (min n s.len) (by
    rw [show min n s.len = if n ≤ s.len then n else s.len from rfl]
    cases s with
    | mk offset len prop =>
    simp only at *
    split_ifs
    case pos h =>
      omega
    case neg h =>
      exact prop
  )

def SliceOf.take_succ {xs: List α} (n: Nat) (s: SliceOf xs) (_h: s.length > 0): SliceOf xs :=
  SliceOf.take (n + 1) s

def SliceOf.drop {xs: List α} (n: Nat) (s: SliceOf xs): SliceOf xs :=
  SliceOf.mk (min (s.offset + n) (s.offset + s.len)) (s.len - n) (by
    cases s with
    | mk offset len prop =>
    simp only at *
    rw [Nat.min_def]
    split_ifs
    case pos h =>
      omega
    case neg h =>
      omega
  )

def SliceOf.drop_succ {xs: List α} (n: Nat) (s: SliceOf xs) (_h: s.length > 0): SliceOf xs :=
  SliceOf.drop (n + 1) s
