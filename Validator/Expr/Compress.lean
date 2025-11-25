import Validator.Std.Vec

import Validator.Expr.Regex
import Validator.Expr.Grammar

namespace Compress

inductive Index n where
 | val (i: Fin n)
 | emptyset -- emptyset is unescapable, so it gets a special index

-- Indices represents compressed indexes
-- that resulted from compressing a list of expressions.
-- This can be used to expanded to a list of expressions.
abbrev Indices (compressed: Nat) (expanded: Nat) :=
  List.Vector (Index compressed) expanded

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
    intro x
    intro hxs
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

def indices [DecidableEq α] {xs: List α} (ys: { ys': List α // ∀ x ∈ xs, x ∈ ys' }): List.Vector (Fin (List.length ys.val)) (List.length xs) :=
  match xs with
  | [] => List.Vector.nil
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
      List.Vector.cons
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
              intro x'
              intro hxs
              cases ys with
              | mk ys hys =>
              simp only
              simp only at hi
              simp_all only [List.mem_cons, forall_eq_or_imp]
            )
          )
        )

def vector_cast (h: n = m) (xs: List.Vector α n): List.Vector α m := by
  subst h
  exact xs

def compress [DecidableEq α] (xs: Rules n (Pred α) l1): Σ l2, ((Rules n (Pred α) l2) × (Indices l2 l1)) :=
  let xs_list: List (Rule n (Pred α)) := xs.toList
  have hn : xs_list.length = l1 := by
    simp_all only [List.Vector.toList_length, xs_list]

  -- sort to increase chance of cache hit
  -- TODO: let sxs := List.mergeSort xs

  -- remove duplicates
  let xs_noreps: { ys: List (Rule n (Pred α)) // ∀ x ∈ xs_list, x ∈ ys } := eraseReps_sub xs_list

  -- get indices
  let xs_idxs: List.Vector (Fin (xs_noreps.val).length) (List.length xs_list) := indices xs_noreps

  -- remove unescapable expressions, currently only emptyset
  -- TODO: let xs_compressed_list := erase xs_noreps Regex.emptyset

  -- find all indexes of the original expressions in the compressed expressions
  let indices: Indices (xs_noreps.val).length (List.length xs_list) := List.Vector.map (fun x => Index.val x) xs_idxs
  let indices': Indices (xs_noreps.val).length l1 := vector_cast hn indices

  Sigma.mk (List.length (xs_noreps.val)) (
    Subtype.mk xs_noreps rfl,
    indices'
  )

def memVector (xs: List.Vector α l) (y: α): Prop :=
  match xs with
  | ⟨[], _⟩ => False
  | ⟨x::xs, h⟩ => x = y \/ memVector ⟨xs, congrArg Nat.pred h⟩ y

instance [DecidableEq α]: Membership α (List.Vector α l) where
  mem := memVector

theorem memVector_nil {n: Nat} {hxs: [].length = n}
  (h : memVector (Subtype.mk [] hxs) y): False := by
  unfold memVector at h
  exact h

theorem length_cons
  (h: (x::xs).length = n): xs.length = n - 1 := by
  simp at h
  omega

theorem memVector_cons {n: Nat} {hxs: (x::xs).length = n}
  (h : memVector (Subtype.mk (x::xs) hxs) y)
  (hnxy : x ≠ y): memVector (Subtype.mk xs (length_cons hxs)) y := by
  simp [memVector] at h
  cases h with
  | inl h =>
    subst_vars
    contradiction
  | inr h =>
    generalize_proofs at h
    exact h

def indexOf' [DecidableEq α] (xs: List.Vector α l) (y: α) (h: y ∈ xs): Fin (xs.length) :=
  match xs with
  | ⟨[], hxs⟩ => by
    exfalso
    apply memVector_nil h
  | ⟨x::xs, hxs⟩ =>
    if hxy: x == y
    then
      Fin.mk 0 (by
        simp [List.Vector.length]
        subst hxs
        simp [List.length]
      )
    else
      let i := indexOf' ⟨xs, congrArg Nat.pred hxs⟩ y (by
        simp only [beq_iff_eq] at hxy
        exact memVector_cons (hxs := hxs) h hxy
      )
      Fin.mk (i.val + 1) (by
        simp [List.Vector.length]
        subst_vars
        omega
      )

theorem memVector_emptyset [DecidableEq α] {y: Regex α}
  (h1 : memVector (Subtype.mk xs hxs) y ∨ y = Regex.emptyset)
  (h2 : ¬y == Regex.emptyset): memVector (Subtype.mk xs hxs) y := by
  cases h1 with
  | inl h =>
    exact h
  | inr h =>
    simp only [beq_iff_eq] at h2
    contradiction

def indexOf [DecidableEq α] (xs: List.Vector (Regex α) l) (y: Regex α) (h: y ∈ xs \/ y = Regex.emptyset): Index (xs.length) :=
  if hy: y == Regex.emptyset
  then Index.emptyset
  else Index.val (indexOf' xs y (memVector_emptyset h hy))

def ofIndex' (xs: Rules n (Pred α) l) (index: Fin l): Rule n (Pred α) :=
  xs.get index

def ofIndex (xs: Rules n (Pred α) l) (index: Index l): Rule n (Pred α) :=
  match index with
  | Index.emptyset => Regex.emptyset
  | Index.val n => ofIndex' xs n

def compressed [DecidableEq σ] (xs: List.Vector (Regex σ) l): Nat :=
  (List.erase (List.eraseReps xs.toList) Regex.emptyset).length

-- theorem compressed_cons_emptyset [DecidableEq σ] (xs: List (Regex σ)):
--   compressed ⟨Regex.emptyset :: xs, h⟩ = compressed ⟨xs, congrArg Nat.pred h⟩ := by
--   sorry

def numReps [DecidableEq α] (xs: List.Vector α l) (x: Option α := Option.none): Nat :=
  match x with
  | Option.none =>
    match xs with
    | ⟨[], _⟩ => 0
    | ⟨x::xs, h⟩ => numReps ⟨xs, congrArg Nat.pred h⟩ (Option.some x)
  | Option.some x =>
    match xs with
    | ⟨[], _⟩ => 0
    | ⟨x'::xs, h⟩ =>
      if x == x'
      then 1 + numReps ⟨xs, congrArg Nat.pred h⟩ (Option.some x')
      else numReps ⟨xs, congrArg Nat.pred h⟩ (Option.some x')

theorem numReps_none_le_length [DecidableEq α] (xs: List.Vector α l):
  numReps xs Option.none <= xs.length := by
  induction xs with
  | nil =>
    simp only [List.Vector.nil, numReps, le_refl]
  | cons ih =>
    rename_i n x xs
    simp [List.Vector.cons]
    split
    simp [numReps]
    unfold numReps
    split
    · omega
    · split_ifs
      case pos h =>
        simp [List.Vector.length]
        rename_i h_2 heq
        subst h_2
        simp_all only [List.length_cons, Subtype.mk.injEq, Nat.add_one_sub_one]
        subst heq
        simp_all only [List.length_cons]
        simp [numReps] at ih
        simp [List.Vector.length] at ih
        omega
      case neg h =>
        rename_i h_2 heq
        subst h_2
        simp_all only [Bool.not_eq_true, List.length_cons, Subtype.mk.injEq, Nat.pred_eq_sub_one, Nat.add_one_sub_one]
        subst heq
        simp_all only [List.length_cons]
        simp [numReps] at ih
        simp [List.Vector.length]
        simp [List.Vector.length] at ih
        omega

theorem numReps_some_le_length [DecidableEq α] (xs: List.Vector α l):
  numReps xs (Option.some y) <= xs.length := by
  induction xs generalizing y with
  | nil =>
    simp only [List.Vector.nil, List.Vector.length]
    unfold numReps
    split
    · omega
    · contradiction
  | cons ih =>
    rename_i n x xs
    simp only [Nat.succ_eq_add_one, List.Vector.cons]
    split
    simp only [List.Vector.length] at *
    rename_i xs xs' hxs'
    simp [numReps]
    split_ifs
    case pos h =>
      simp only at h
      subst_vars
      have ih' := ih (y := y)
      omega
    case neg h =>
      generalize_proofs
      have ih' := ih (y := x)
      omega

theorem numReps_le_length [DecidableEq α] (xs: List.Vector α l) (y: Option α):
  numReps xs y <= xs.length := by
  cases y with
  | none =>
    apply numReps_none_le_length
  | some y =>
    apply numReps_some_le_length

-- def eraseReps [DecidableEq α] (xs: List.Vector α l) (x: Option α := Option.none): List.Vector α (l - numReps xs x) :=
--   match x with
--   | Option.none =>
--     match xs with
--     | ⟨[], h⟩ => ⟨[], by
--         subst h
--         simp only [List.length_nil, zero_tsub]
--       ⟩
--     | ⟨x::xs, h⟩ => ⟨
--         x :: (eraseReps ⟨xs, congrArg Nat.pred h⟩ (Option.some x)).val, by
--         subst h
--         simp only [numReps]
--         simp only [
--           List.length_cons,
--           Nat.pred_eq_sub_one,
--           List.Vector.length_val,
--         ]
--         rename_i xs'
--         generalize_proofs hxs'
--         have hnone := numReps_le_length ⟨xs', hxs'⟩ none
--         have hsome := numReps_le_length ⟨xs', hxs'⟩ (some x)
--         simp only [List.Vector.length] at hsome
--         simp only [List.Vector.length] at hnone
--         omega
--       ⟩
--   | Option.some x =>
--     match xs with
--     | ⟨[], h⟩ => ⟨[], by
--         subst h
--         simp only [List.length_nil, zero_tsub]
--       ⟩
--     | ⟨x'::xs, h⟩ =>
--       if heq: x == x'
--       then ⟨(eraseReps ⟨xs, congrArg Nat.pred h⟩ (Option.some x')).val, by
--         simp only [Nat.pred_eq_sub_one, List.Vector.length_val]
--         subst h
--         rename_i xs'
--         simp only [numReps]
--         simp at heq
--         split_ifs
--         case pos h =>
--           subst heq
--           omega
--         case neg h =>
--           simp at h
--           contradiction
--       ⟩
--       else ⟨x :: (eraseReps ⟨xs, congrArg Nat.pred h⟩ (Option.some x')).val, by
--         simp only [Nat.pred_eq_sub_one, List.length_cons, List.Vector.length_val]
--         simp [numReps]
--         split_ifs
--         case pos h =>
--           simp at heq
--           contradiction
--         case neg h =>
--           rename_i hlen
--           subst hlen
--           simp
--           rename_i xs'
--           generalize_proofs hxs'
--           have hnone := numReps_le_length ⟨xs', hxs'⟩ none
--           have hsome := numReps_le_length ⟨xs', hxs'⟩ (some x')
--           simp only [List.Vector.length] at hsome
--           simp only [List.Vector.length] at hnone
--           rw [Nat.sub_add_comm hsome]
--       ⟩

def smallest [DecidableEq α] [LT α] [DecidableLT α] (xs: List.Vector α l) (y: α): Option (Fin l) :=
  match xs with
  | ⟨[], h⟩ => Option.none
  | ⟨x::xs, h⟩ =>
    if x < y
    then
      match smallest ⟨xs, congrArg Nat.pred h⟩ x with
      | Option.none => Option.some ⟨0, by
          subst h
          simp
        ⟩
      | Option.some n => Option.some ⟨n + 1, by
          subst h
          simp
        ⟩
    else
      match smallest ⟨xs, congrArg Nat.pred h⟩ y with
      | Option.none => Option.none
      | Option.some n => Option.some ⟨n + 1, by
          subst h
          simp
        ⟩

-- def comp [DecidableEq σ] [LT (Regex σ)] [DecidableLT (Regex σ)] (xs: List.Vector (Regex σ) l) (dup: Option (Regex σ) := Option.none): (List.Vector (Regex σ) (compressed xs)) × (Indices l (compressed xs)) :=
--   match xs with
--   | ⟨[], h⟩ => (⟨[], by simp [compressed, List.eraseReps, List.eraseRepsBy]⟩, ⟨[], h⟩)
--   | ⟨x::xs, h⟩ =>
--     match smallest ⟨xs, congrArg Nat.pred h⟩ x with
--     | Option.none =>
--       match dup with
--       | Option.none =>
--         match x with
--         | Regex.emptyset =>
--           let (regexes, indices) := comp ⟨xs, congrArg Nat.pred h⟩ (Option.some x)
--           (⟨regexes.val, by

--           ⟩ , List.Vector.cons Index.emptyset (indices))
--         | _ =>
--           sorry
--       | Option.some dup => sorry
--     | Option.some i => sorry

def compressM [DecidableEq α] [Monad m] (xs: Rules n (Pred α) l1): m (Σ l2, (Rules n (Pred α) l2) × Indices l2 l1) := do
  return compress xs

-- expand expands a list of expressions.
def expand (indices: Indices l1 l2) (xs: Rules n (Pred α) l1): (Rules n (Pred α) l2) :=
  List.Vector.map (ofIndex xs) indices

def expandM [Monad m] (indices: Indices l1 l2) (xs: Rules n (Pred α) l1): m (Rules n (Pred α) l2) :=
  return (expand indices xs)
