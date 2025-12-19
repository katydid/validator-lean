import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Hedge.Grammar

namespace Compress

inductive Index n where
 | val (i: Fin n)
 | emptyset -- emptyset is unescapable, so it gets a special index

-- Indices represents compressed indexes
-- that resulted from compressing a list of expressions.
-- This can be used to expanded to a list of expressions.
abbrev Indices (compressed: Nat) (expanded: Nat) :=
  Vec (Index compressed) expanded

def eraseReps' [DecidableEq α] (x: α) (xs: List α): List α :=
  match xs with
  | [] => [x]
  | (x'::xs) =>
    if x == x'
    then eraseReps' x' xs
    else x :: eraseReps' x' xs

def eraseReps [DecidableEq α] (xs: List α): List α :=
  match xs with
  | [] => []
  | (x::xs) => eraseReps' x xs

theorem eraseReps_member [DecidableEq α] {xs: List α}:
  (x ∈ xs) -> (x ∈ eraseReps xs) := by
  unfold eraseReps
  intro hxs
  cases xs with
  | nil =>
    simp at hxs
  | cons x' xs =>
    simp
    fun_induction eraseReps'
    case case1 x' =>
      assumption
    case case2 x' x'' xs hc ih =>
      simp at hc
      subst hc
      apply ih
      simp_all only [List.mem_cons, or_self_left]
    case case3 x' x'' xs hc ih =>
      simp at hc
      simp at hxs
      simp
      -- aesop?
      simp_all only [List.mem_cons]
      cases hxs with
      | inl h =>
        subst h
        simp_all only [false_or, true_or]
      | inr h_1 =>
        cases h_1 with
        | inl h =>
          subst h
          simp_all only [true_or, forall_const, or_true]
        | inr h_2 => simp_all only [or_true, forall_const]

def eraseReps_sub [DecidableEq α] (xs: List α): { ys: List α // ∀ x ∈ xs, x ∈ ys } :=
  let ys := eraseReps xs
  Subtype.mk ys (by
    subst ys
    intro x hxs
    apply eraseReps_member hxs
  )

def idxOf? [DecidableEq α] (xs : List α) (y: α) (i : Nat := 0) : Option Nat :=
  match xs with
  | [] => Option.none
  | (x::xs) =>
    if x == y
    then Option.some i
    else idxOf? xs y (i + 1)

theorem idxOf_length' [DecidableEq α] {y: α} (h: idxOf? xs y n = some i):
  i < List.length xs + n := by
  induction xs generalizing i n with
  | nil =>
    simp [idxOf?] at h
  | cons x xs ih =>
    simp [idxOf?] at h
    split_ifs at h
    case pos hxy =>
      simp_all
    case neg hxy =>
      simp_all
      have ih' := @ih (n + 1)
      rw [Nat.add_assoc]
      nth_rewrite 2 [Nat.add_comm]
      apply ih' h

theorem idxOf_length [DecidableEq α] {y: α} (h: idxOf? xs y = some i):
  i < List.length xs := by
  apply idxOf_length' (n := 0) h

theorem idxOf?_eq_none_iff' [DecidableEq α] {xs : List α} {y : α} :
  idxOf? xs y i = none ↔ y ∉ xs := by
  induction xs generalizing i with
  | nil =>
    simp [idxOf?]
  | cons x xs ih =>
    simp [idxOf?]
    split_ifs
    case pos h =>
      subst_vars
      -- aesop?
      simp_all only [not_true_eq_false, false_and]
    case neg h =>
      have ih' := ih (i := i + 1)
      -- aesop?
      simp_all only [iff_and_self]
      intro a
      simp_all only [not_false_eq_true, iff_true]
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      subst a_1
      simp_all only [not_true_eq_false]

theorem idxOf?_eq_none_iff [DecidableEq α] {xs : List α} {y : α} :
  idxOf? xs y = none ↔ y ∉ xs := by
  apply idxOf?_eq_none_iff' (i := 0)

def indices [DecidableEq α] {xs: List α} (ys: { ys': List α // ∀ x ∈ xs, x ∈ ys' }): Vec (Fin (List.length ys.val)) (List.length xs) :=
  match xs with
  | [] => Vec.nil
  | (x::xs) =>
    match hi: idxOf? ys.val x with
    | Option.none => by
      cases ys with
      | mk ys hys =>
      simp only [List.mem_cons, forall_eq_or_imp] at hys
      obtain ⟨left, right⟩ := hys
      simp only at hi
      simp_all only [idxOf?_eq_none_iff, List.mem_cons, true_or, not_true_eq_false]
    | Option.some i =>
      Vec.cons
        (
          Fin.mk
            i
            (by
              cases ys with
              | mk ys hys =>
              simp only
              simp only [List.mem_cons, forall_eq_or_imp] at hys
              obtain ⟨left, right⟩ := hys
              simp only at hi
              apply idxOf_length hi
            )
        )
        (indices (xs := xs)
          (Subtype.mk
            ys.val
            (by
              intro x' hxs
              cases ys with
              | mk ys hys =>
              simp only
              simp only at hi
              simp_all only [List.mem_cons, forall_eq_or_imp]
            )
          )
        )

def compress [DecidableEq φ] (xs: Rules n φ l1): Σ l2, ((Rules n φ l2) × (Indices l2 l1)) :=
  let xs_list: List (Rule n φ) := xs.toList
  have hn : xs_list.length = l1 := by
    simp_all only [Vec.toList_length, xs_list]

  -- sort to increase chance of cache hit
  -- TODO: let sxs := List.mergeSort xs

  -- remove duplicates
  let xs_noreps: { ys: List (Rule n φ) // ∀ x ∈ xs_list, x ∈ ys } := eraseReps_sub xs_list

  -- get indices
  let xs_idxs: Vec (Fin (xs_noreps.val).length) (List.length xs_list) := indices xs_noreps

  -- remove unescapable expressions, currently only emptyset
  -- TODO: let xs_compressed_list := erase xs_noreps Regex.emptyset

  -- find all indexes of the original expressions in the compressed expressions
  let indices: Indices (xs_noreps.val).length (List.length xs_list) := Vec.map xs_idxs (fun x => Index.val x)
  let indices': Indices (xs_noreps.val).length l1 := Vec.cast indices hn

  Sigma.mk (List.length (xs_noreps.val)) (
    Vec.fromList xs_noreps.val,
    indices'
  )

theorem length_cons
  (h: (x::xs).length = n): xs.length = n - 1 := by
  simp at h
  omega

theorem mem_emptyset [DecidableEq α] {y: Regex α} {xs: Vec (Regex α) l}
  (h1 : y ∈ xs ∨ y = Regex.emptyset)
  (h2 : ¬y == Regex.emptyset): y ∈ xs := by
  cases h1 with
  | inl h =>
    exact h
  | inr h =>
    simp only [beq_iff_eq] at h2
    contradiction

def indexOf [DecidableEq α] (xs: Vec (Regex α) l) (y: Regex α) (h: y ∈ xs \/ y = Regex.emptyset): Index l :=
  if hy: y == Regex.emptyset
  then Index.emptyset
  else Index.val (Vec.indexOf xs y (mem_emptyset h hy))

def ofIndex' (xs: Rules n φ l) (index: Fin l): Rule n φ :=
  xs.get index

def ofIndex (xs: Rules n φ l) (index: Index l): Rule n φ :=
  match index with
  | Index.emptyset => Regex.emptyset
  | Index.val n => ofIndex' xs n

def compressed [DecidableEq σ] (xs: Vec (Regex σ) l): Nat :=
  (List.erase (List.eraseReps xs.toList) Regex.emptyset).length

def compressM [DecidableEq φ] [Monad m] (xs: Rules n φ l1): m (Σ l2, (Rules n φ l2) × Indices l2 l1) := do
  return compress xs

-- expand expands a list of expressions.
def expand (indices: Indices l1 l2) (xs: Rules n φ l1): (Rules n φ l2) :=
  Vec.map indices (ofIndex xs)

def expandM [Monad m] (indices: Indices l1 l2) (xs: Rules n φ l1): m (Rules n φ l2) :=
  return (expand indices xs)
