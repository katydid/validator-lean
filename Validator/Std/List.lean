import Mathlib.Tactic.NthRewrite

namespace List

theorem list_elem_lt [SizeOf α] {xs: List α} (h: x ∈ xs): sizeOf x ≤ sizeOf xs := by
  rw [show (x ∈ xs) = List.Mem x xs from rfl] at h
  induction h with
  | head xs' =>
    simp +arith
  | tail _ _ ih =>
    apply Nat.le_trans ih
    simp +arith

theorem list_foldl_attach {f: β -> α -> β} {init: β} {xs: List α}:
  List.foldl (fun res ⟨x, _hx⟩ => f res x) init (List.attach xs)
  = List.foldl f init xs := by
  simp only [foldl_subtype, unattach_attach]

theorem list_splitAt_n: xs = (List.splitAt n xs).1 ++ (List.splitAt n xs).2 := by
  simp only [List.splitAt_eq, List.take_append_drop]

theorem list_splitAt_fst_take: (List.splitAt n xs).1 = take n xs := by
  simp only [List.splitAt_eq]

theorem list_splitAt_snd_drop: (List.splitAt n xs).2 = drop n xs := by
  simp only [List.splitAt_eq]

theorem list_take_drop_n: xs = List.take n xs ++ List.drop n xs := by
  simp only [List.take_append_drop]

theorem list_sizeOf_prepend [SizeOf α] (xs ys: List α):
  sizeOf xs <= sizeOf (ys ++ xs) := by
  induction ys with
  | nil =>
    simp only [List.nil_append, Nat.le_refl]
  | cons y ys ih =>
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    omega

theorem list_sizeOf_insert [SizeOf α] (xs ys: List α):
  sizeOf (y::xs ++ ys) = sizeOf (xs ++ y::ys) := by
  induction xs with
  | nil =>
    simp [List.cons.sizeOf_spec]
  | cons x xs ih =>
    simp [List.cons.sizeOf_spec]
    rw [<- ih]
    simp +arith [List.cons.sizeOf_spec]

theorem list_sizeOf_append [SizeOf α] (xs ys: List α):
  sizeOf xs <= sizeOf (xs ++ ys) := by
  induction ys with
  | nil =>
    simp only [append_nil, Nat.le_refl]
  | cons y ys ih =>
    rw [<- list_sizeOf_insert]
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    omega

theorem list_sizeOf_cons [SizeOf α] (xs ys: List α):
  sizeOf xs < sizeOf (y::ys ++ xs) := by
  induction ys with
  | nil =>
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    simp only [List.nil_append, Nat.le_add_left]
  | cons y ys ih =>
    simp only [List.cons_append] at *
    simp only [List.cons.sizeOf_spec] at *
    omega

theorem list_length_neq_take {n: Nat} {xs: List α}:
  ¬List.take n xs = xs -> (List.take n xs).length < xs.length := by
  intro h
  fun_induction List.take
  case case1 xs =>
    simp
    cases xs with
    | nil =>
      simp at h
    | cons x xs =>
      simp
  case case2 =>
    simp at h
  case case3 n x xs h' =>
    simp at h
    have h' := h' h
    simp only [length_cons]
    omega

theorem list_length_neq_drop {n: Nat} {xs: List α}:
  ¬List.drop n xs = xs -> (List.drop n xs).length < xs.length := by
  intro h
  induction n with
  | zero =>
    simp at h
  | succ n =>
    cases xs with
    | nil =>
      simp at h
    | cons x xs =>
      simp
      omega

theorem list_sizeOf_slice [SizeOf α] (xs ys zs: List α):
  sizeOf ys <= sizeOf (xs ++ (ys ++ zs)) := by
  induction xs with
  | nil =>
    simp only [nil_append]
    apply list_sizeOf_append ys zs
  | cons x xs ih =>
    simp [List.cons.sizeOf_spec]
    omega

theorem list_drop_exists (n: Nat) (xs: List α): ∃ ys, xs = ys ++ (List.drop n xs) := by
  induction n with
  | zero =>
    exists []
  | succ n ih =>
    cases ih with
    | intro ys ih =>
      cases xs with
      | nil =>
        simp at *
      | cons x xs =>
        simp only [List.drop_succ_cons]
        exists (x::List.take n xs)
        simp

theorem list_self_neq_cons_append:
  xs ≠ y :: (ys ++ xs) := by
  intro h
  rw [←List.cons_append] at h
  rw [List.self_eq_append_left] at h
  nomatch h

theorem list_drop_neq_cons:
  List.drop n xs ≠ x :: xs := by
  have h := list_drop_exists n xs
  cases h with
  | intro ys h =>
  nth_rewrite 2 [h]
  simp
  exact list_self_neq_cons_append (xs := drop n xs) (y := x) (ys := ys)

theorem list_sizeOf_take_drop_le [SizeOf α] (xs: List α):
  sizeOf (List.take t (List.drop d xs)) <= sizeOf xs := by
  induction xs generalizing t d with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.cons.sizeOf_spec]
    cases d with
    | zero =>
      simp
      cases t with
      | zero =>
        simp
        omega
      | succ t =>
        simp
        have ih' := @ih t 0
        simp at ih'
        assumption
    | succ d =>
      simp
      have ih' := @ih t d
      omega
