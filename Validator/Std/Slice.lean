import Validator.Std.List
import Validator.Std.Nat

import Mathlib.Data.Quot
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.RewriteSearch

structure Slice (α: Type) where
  data: List α
  off: Nat
  len: Nat

def LawfulSlice (α: Type) := { s: Slice α // s.off + s.len <= s.data.length }

def LawfulSlice.mk (data: List α) (off: Nat) (len: Nat) (p: off + len <= data.length): LawfulSlice α :=
  Subtype.mk (Slice.mk data off len) p

def LawfulSlice.fromList (xs: List α): LawfulSlice α :=
  Subtype.mk (Slice.mk xs 0 xs.length) (by
    simp only [Nat.zero_add, Nat.le_refl]
  )

def LawfulSlice.isEmpty (s: LawfulSlice α): Bool :=
  s.val.len = 0

def LawfulSlice.toList (s: LawfulSlice α): List α :=
  List.take s.val.len (List.drop s.val.off s.val.data)

def LawfulSlice.data (s: LawfulSlice α): List α :=
  s.val.data

def LawfulSlice.length (s: LawfulSlice α): Nat :=
  s.val.len

def LawfulSlice.offset (s: LawfulSlice α): Nat :=
  s.val.off

def LawfulSlice.bounds {α} (s: LawfulSlice α): s.offset + s.length <= s.data.length :=
  s.property

def LawfulSlice.nonEmpty {α: Type} (s: LawfulSlice α): Option {s': LawfulSlice α // s'.length > 0} :=
  match h: s.val.len with
  | 0 => Option.none
  | l + 1 => Option.some (Subtype.mk s (by
    simp only [length, gt_iff_lt]
    omega
  ))

def LawfulSlice.take (n: Nat) (s: LawfulSlice α): LawfulSlice α :=
  LawfulSlice.mk s.data s.offset (min n s.length) (by
    rw [show min n s.length = if n ≤ s.length then n else s.length from rfl]
    obtain ⟨⟨d, o, l⟩, hs⟩ := s
    simp only at hs
    simp only [offset, length, data]
    split_ifs
    case pos h =>
      omega
    case neg h =>
      exact hs
  )

def LawfulSlice.drop (n: Nat) (s: LawfulSlice α): LawfulSlice α :=
  LawfulSlice.mk s.data (min (s.offset + n) (s.offset + s.length)) (s.length - n) (by
    obtain ⟨⟨ data, offset, len⟩, prop⟩ := s
    simp only at prop
    simp only [LawfulSlice.offset, length, Nat.add_min_add_left, LawfulSlice.data]
    rw [Nat.min_def]
    split_ifs
    case pos h =>
      omega
    case neg h =>
      omega
  )

theorem LawfulSlice.take_is_List.take {xs: List α}:
  (LawfulSlice.take n (LawfulSlice.fromList xs)).toList = List.take n xs := by
  simp only [toList, LawfulSlice.take, mk, data, fromList, offset, length, List.drop_zero,
    List.take_eq_take_iff, Nat.min_assoc, Nat.le_refl, Nat.min_eq_left]

theorem LawfulSlice.drop_is_List.drop {xs: List α}:
  (LawfulSlice.drop n (LawfulSlice.fromList xs)).toList = List.drop n xs := by
  simp only [toList, LawfulSlice.drop, mk, data, fromList, offset, Nat.zero_add, length]
  rw [Nat.nat_min]
  split_ifs
  case pos h =>
    rw [List.list_take_eq_self_iff]
    rw [List.length_drop]
    omega
  case neg h =>
    simp only [List.drop_length, List.take_nil, List.nil_eq, List.drop_eq_nil_iff]
    omega

theorem LawfulSlice.take_zero_is_empty {xs: List α}:
  (LawfulSlice.take 0 (LawfulSlice.fromList xs)).nonEmpty = Option.none := by
  simp only [LawfulSlice, length, nonEmpty, fromList, take, data, offset, mk, Nat.succ_eq_add_one,
    Nat.zero_le, Nat.min_eq_left]
  split
  · rfl
  · omega

theorem LawfulSlice.take_nil_is_empty {α: Type}:
  (LawfulSlice.take n (@LawfulSlice.fromList α [])).nonEmpty = Option.none := by
  simp only [LawfulSlice, length, nonEmpty, fromList, List.length_nil, take, data, offset, mk,
    Nat.succ_eq_add_one, Nat.zero_le, Nat.min_eq_right]
  split
  · rfl
  · omega

-- Quotient

abbrev eqv {α: Type} (s1 s2 : LawfulSlice α) : Prop :=
  s1.toList = s2.toList

infix:50 " ~ " => eqv

example:
  LawfulSlice.fromList [1,2,3] ~ (LawfulSlice.fromList [1,2,3,4]).take 3 := by
  unfold eqv
  rw [LawfulSlice.take_is_List.take]
  simp only [LawfulSlice.toList, LawfulSlice.fromList, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd, List.drop_zero, List.take_succ_cons, List.take_nil, List.take_zero]

private theorem eqv.refl {α: Type} (s : LawfulSlice α) : s ~ s := rfl

private theorem eqv.symm {α: Type} : ∀ {s1 s2 : LawfulSlice α},
  s1 ~ s2 → s2 ~ s1 := by
  intro r1 r2 h
  unfold eqv at *
  rw [h]

private theorem eqv.trans {α: Type} : ∀ {s1 s2 s3 : LawfulSlice α}, s1 ~ s2 → s2 ~ s3 → s1 ~ s3 := by
  unfold eqv
  intro s1 s2 s3 s1s2 s2s3
  rw [s1s2, s2s3]

instance IsEquivalence_LawfulSlice {α: Type} : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

instance IsSetoid_LawfulSlice (α: Type): Setoid (LawfulSlice α) where
   r     := eqv
   iseqv := IsEquivalence_LawfulSlice

instance {α : Sort u} [Setoid α] : HasEquiv α :=
   ⟨Setoid.r⟩

theorem LawfulSlice.refl {α: Type} (a : LawfulSlice α) : a ≈ a :=
  IsEquivalence_LawfulSlice.refl a

theorem LawfulSlice.symm {α: Type} {a b : LawfulSlice α} (hab : a ≈ b) : b ≈ a :=
  IsEquivalence_LawfulSlice.symm hab

theorem LawfulSlice.trans {α: Type} {a b c : LawfulSlice α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  IsEquivalence_LawfulSlice.trans hab hbc

def LawfulSliceQ (α: Type): Type :=
  Quotient (IsSetoid_LawfulSlice α)

def LawfulSliceQ.fromLawfulSlice' {α: Type} (x: LawfulSlice α): LawfulSliceQ α  :=
  Quot.mk Setoid.r x

def LawfulSliceQ.fromLawfulSlice {α: Type} (x: LawfulSlice α): LawfulSliceQ α :=
  Quotient.mk' x

def LawfulSliceQ.fromList {α: Type} (data: List α): LawfulSliceQ α :=
  Quotient.mk' (LawfulSlice.fromList data)

theorem LawfulSlice.isEmpty_respects_eqv {α: Type}:
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.isEmpty x) = (LawfulSlice.isEmpty y) := by
  intro x y h
  unfold LawfulSlice.isEmpty
  unfold eqv at h
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [toList] at h
  simp only [decide_eq_decide]
  apply Iff.intro
  case mp =>
    intro hxl
    subst_vars
    simp only [Nat.add_zero] at xp
    simp only at yp
    simp only [List.take_zero, List.nil_eq, List.take_eq_nil_iff, List.drop_eq_nil_iff] at h
    cases h
    · omega
    · omega
  case mpr =>
    intro hyl
    subst_vars
    simp only at xp
    simp only [Nat.add_zero] at yp
    simp only [List.take_zero, List.take_eq_nil_iff, List.drop_eq_nil_iff] at h
    omega

def LawfulSliceQ.isEmpty {α: Type} (s: LawfulSliceQ α): Bool :=
  Quotient.lift LawfulSlice.isEmpty LawfulSlice.isEmpty_respects_eqv s

theorem List.eq_slice_eq_length
  {xo xl: Nat} {xd: List α} (hx : xo + xl ≤ xd.length)
  {yo yl: Nat} {yd: List α} (hy : yo + yl ≤ yd.length)
  (h : List.take xl (List.drop xo xd) = List.take yl (List.drop yo yd)):
  xl = yl := by
  rw [← List.Sublist.length_eq (by rw [h]; simp only [Sublist.refl])] at h
  simp only [length_take, length_drop] at h
  rw [Nat.min_def] at h
  rw [Nat.min_def] at h
  rw [← Nat.le_sub_iff_add_le' (by omega)] at hx
  rw [← Nat.le_sub_iff_add_le' (by omega)] at hy
  split_ifs at h
  assumption

theorem LawfulSlice.length_respects_eqv {α: Type}:
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.length x) = (LawfulSlice.length y) := by
  intro x y h
  unfold LawfulSlice.length
  unfold eqv at h
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [toList] at xp yp h
  simp only
  apply @List.eq_slice_eq_length α xo xl xd xp yo yl yd yp h

def LawfulSliceQ.length {α: Type} (s: LawfulSliceQ α): Nat :=
  Quotient.lift LawfulSlice.length LawfulSlice.length_respects_eqv s

theorem LawfulSlice.toList_respects_eqv {α: Type}:
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.toList x) = (LawfulSlice.toList y) := by
  intro x y h
  unfold eqv at h
  unfold LawfulSlice.toList
  simp only [toList] at h
  exact h

def LawfulSliceQ.toList {α: Type} (s: LawfulSliceQ α): List α :=
  Quotient.lift LawfulSlice.toList LawfulSlice.toList_respects_eqv s

private theorem ite_add (P : Prop) [Decidable P] (a b c : Nat) :
  (if P then a else b) + c = if P then a + c else b + c := by
  split_ifs <;> rfl

theorem List.take_min_eq_take_take:
  List.take (min a b) xs = List.take a (List.take b xs) := by
  rw [Nat.min_def]
  fun_induction List.take generalizing a
  case case1 =>
    simp only [Nat.le_zero_eq, take_nil, take_eq_nil_iff, ite_eq_right_iff, imp_self, true_or]
  case case2 =>
    simp only [Nat.succ_eq_add_one, take_nil]
  case case3 b x xs ih =>
    cases a with
    | zero =>
      simp only [Nat.succ_eq_add_one, Nat.le_add_left, ↓reduceIte, take_zero]
    | succ a =>
      simp only [Nat.succ_eq_add_one, Nat.add_le_add_iff_right, take_succ_cons]
      rw [<- ih]
      rw [← ite_add (a ≤ b) a b 1]
      simp only [take_succ_cons]

theorem List.take_respects_eqv
  (h: List.take xl (List.drop xo data) = List.take yl (List.drop yo data)):
  List.take (min n xl) (List.drop xo data) = List.take (min n yl) (List.drop yo data) := by
  rw [List.take_min_eq_take_take]
  rw [List.take_min_eq_take_take]
  rw [h]

theorem LawfulSlice.take_respects_eqv {α: Type} (n: Nat):
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.take n x) ~ (LawfulSlice.take n y) := by
  unfold eqv
  intro x y
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [LawfulSlice.take]
  simp only [toList, mk, data, offset, length]
  simp only at xp
  simp only at yp
  intro hxy
  have h' := @List.eq_slice_eq_length α xo xl xd xp yo yl yd yp hxy
  subst_vars
  rw [List.take_min_eq_take_take]
  rw [List.take_min_eq_take_take]
  rw [hxy]

theorem LawfulSliceQ.take_respects_eqv {α: Type} (n: Nat):
  ∀ (x y: LawfulSlice α), x ~ y ->
    (Quotient.mk' (LawfulSlice.take n x)) = (Quotient.mk' (LawfulSlice.take n y)) := by
  simp only [Quotient.eq']
  simp only [IsSetoid_LawfulSlice]
  apply LawfulSlice.take_respects_eqv

def LawfulSliceQ.take {α: Type} (n: Nat) (s: LawfulSliceQ α): LawfulSliceQ α :=
  Quotient.lift (fun xs => (Quotient.mk' (LawfulSlice.take n xs))) (LawfulSliceQ.take_respects_eqv n) s

theorem min_sub_is_pos (n m: Nat):
  (min n m + (m - n)) = m := by
  rw [Nat.min_def]
  split_ifs
  case pos =>
    omega
  case neg =>
    omega

theorem List.drop_respects_eqv
  (hx : xo + xl ≤ data.length)
  (hy : yo + yl ≤ data.length)
  (h: List.take xl (List.drop xo data) = List.take yl (List.drop yo data)):
  List.take (xl - n) (List.drop (min (xo + n) (xo + xl)) data) =
    List.take (yl - n) (List.drop (min (yo + n) (yo + yl)) data) := by
  rw [Nat.add_min_add_left]
  rw [Nat.add_min_add_left]
  rw [<- List.drop_drop]
  rw [<- List.drop_drop]
  rw [take_drop]
  rw [min_sub_is_pos]
  nth_rewrite 2 [take_drop]
  rw [min_sub_is_pos]
  rw [h]
  have hl := List.eq_slice_eq_length hx hy h
  rw [hl]

theorem LawfulSlice.drop_respects_eqv {α: Type} (n: Nat):
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.drop n x) ~ (LawfulSlice.drop n y) := by
  unfold eqv
  intro x y
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [LawfulSlice.drop]
  simp only [toList, mk, data, offset, length, Nat.add_min_add_left]
  simp only at xp
  simp only at yp
  intro hxy
  have h' := @List.eq_slice_eq_length α xo xl xd xp yo yl yd yp hxy
  subst_vars
  rw [← List.drop_drop]
  rw [← List.drop_drop]
  rw [List.take_drop]
  nth_rewrite 2 [List.take_drop]
  nth_rw 2 [min_sub_is_pos n yl]
  nth_rw 1 [min_sub_is_pos n yl]
  rw [hxy]

theorem LawfulSliceQ.drop_respects_eqv {α: Type} (n: Nat):
  ∀ (x y: LawfulSlice α), x ~ y ->
    (Quotient.mk' (LawfulSlice.drop n x)) = (Quotient.mk' (LawfulSlice.drop n y)) := by
  simp only [Quotient.eq']
  simp only [IsSetoid_LawfulSlice]
  apply LawfulSlice.drop_respects_eqv

def LawfulSliceQ.drop {α: Type} (n: Nat) (s: LawfulSliceQ α): LawfulSliceQ α :=
  (Quotient.lift (fun xs => (Quotient.mk' (LawfulSlice.drop n xs)))) (LawfulSliceQ.drop_respects_eqv n) s

theorem LawfulSliceQ.take_fromList_eq_fromList_take {α: Type} {n: Nat} {xs: List α}:
  (LawfulSliceQ.take n (LawfulSliceQ.fromList xs))
  = (LawfulSliceQ.fromList (List.take n xs)) := by
  unfold LawfulSliceQ.take
  apply Quot.sound
  simp only [LawfulSlice, IsSetoid_LawfulSlice, LawfulSlice.take, LawfulSlice.mk, LawfulSlice.data,
    LawfulSlice.fromList, LawfulSlice.offset, LawfulSlice.length, List.length_take]
  unfold eqv
  simp only [LawfulSlice.toList, List.drop_zero]
  rw [List.take_take]
  rw [Nat.min_right_comm n xs.length n]
  rw [Nat.min_self n]

theorem LawfulSliceQ.length_respects_eqv {α: Type}:
   ∀ (xs: LawfulSlice α),
    (LawfulSlice.length xs) = (LawfulSliceQ.length (LawfulSliceQ.fromLawfulSlice xs)) := by
  intro xs
  unfold LawfulSliceQ.fromLawfulSlice
  unfold Quotient.mk'
  unfold LawfulSliceQ.length
  simp only [LawfulSlice.length, LawfulSlice, Quotient.mk]

def Quotient.fromOptionSubtype
  (s: Option {ys: LawfulSlice α // ys.length > 0}):
  Option {ys: LawfulSliceQ α // ys.length > 0} :=
  match s with
  | Option.none => Option.none
  | Option.some s => Option.some (
    match s with
    | Subtype.mk ys hys =>
      Subtype.mk (LawfulSliceQ.fromLawfulSlice ys) (by
        simp only at hys
        rw [LawfulSliceQ.length_respects_eqv] at hys
        exact hys
      )
    )

theorem LawfulSliceQ.nonEmpty_respects_eqv {α: Type}:
  ∀ (x y: LawfulSlice α), x ~ y ->
    (Quotient.fromOptionSubtype (LawfulSlice.nonEmpty x)) = (Quotient.fromOptionSubtype (LawfulSlice.nonEmpty y)) := by
  unfold eqv
  simp only [Quotient.fromOptionSubtype]
  intro x y hxy
  simp only [LawfulSlice.nonEmpty]
  simp only [LawfulSlice, LawfulSlice.length, Nat.succ_eq_add_one, fromLawfulSlice]
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [LawfulSlice.toList] at hxy
  simp only at yp
  simp only at xp
  have hl := @List.eq_slice_eq_length α xo xl xd xp yo yl yd yp hxy
  subst_vars
  cases yl with
  | zero =>
    simp only
  | succ yl =>
    simp only [Option.some.injEq, Subtype.mk.injEq]
    apply Quot.sound
    simp only [IsSetoid_LawfulSlice, LawfulSlice]
    simp only [eqv, LawfulSlice.toList]
    exact hxy

def LawfulSliceQ.nonEmpty {α: Type} (s: LawfulSliceQ α):
  Option {ys: LawfulSliceQ α // ys.length > 0} :=
  (Quotient.lift (fun xs => (Quotient.fromOptionSubtype (LawfulSlice.nonEmpty xs)))) LawfulSliceQ.nonEmpty_respects_eqv s
