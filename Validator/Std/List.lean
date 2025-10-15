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

theorem list_length_drop_lt_cons {n: Nat} {xs: List α}:
  (List.drop n xs).length < (x :: xs).length := by
  simp only [length_drop, length_cons]
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
  cases n with
  | zero =>
    rw [drop_zero]
    exists []
  | succ n' =>
    cases xs with
    | nil =>
      rewrite [drop_nil]
      exists []
    | cons x xs =>
      simp only [List.drop_succ_cons]
      exists (x::List.take n' xs)
      simp only [cons_append]
      congr
      simp only [take_append_drop]

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

theorem list_take_n_nil {n: Nat} {α: Type}:
  @List.take α n [] = [] := by
  simp

theorem list_infix_take_is_infix:
  List.IsInfix xs (List.take n ys) ->
  List.IsInfix xs ys := by
  intro h
  have hys := List.infix_append [] (List.take n ys) (List.drop n ys)
  simp at hys
  apply List.IsInfix.trans h hys

theorem list_infix_drop_is_infix:
  List.IsInfix xs (List.drop n ys) ->
  List.IsInfix xs ys := by
  intro h
  have hys := List.infix_append (List.take n ys) (List.drop n ys) []
  simp at hys
  apply List.IsInfix.trans h hys

theorem list_infix_def {xs ys: List α}:
  List.IsInfix xs ys ->
  ∃ xs1 xs2, xs1 ++ xs ++ xs2 = ys := by
  intro h
  obtain ⟨xs1, h⟩ := h
  obtain ⟨xs2, h⟩ := h
  exists xs1
  exists xs2

abbrev InfixOf {α: Type} (xs: List α) := { ys: List α // List.IsInfix ys xs }

def InfixOf.mk {α: Type} {xs: List α} (ys: List α) (property : List.IsInfix ys xs) : InfixOf xs :=
  (Subtype.mk ys property)

def InfixOf.self (xs: List α): InfixOf xs :=
  Subtype.mk xs (by simp only [List.infix_rfl])

theorem list_infixof_take_is_infix {xs: List α} (ys: InfixOf (List.take n xs)):
  List.IsInfix ys.val xs := by
  obtain ⟨ys, hys⟩ := ys
  simp
  have h1 := list_infix_take_is_infix hys
  assumption

theorem list_infixof_drop_is_infix {xs: List α} (ys: InfixOf (List.drop n xs)):
  List.IsInfix ys.val xs := by
  obtain ⟨ys, hys⟩ := ys
  simp
  have h1 := list_infix_drop_is_infix hys
  assumption

theorem list_infix_is_leq_sizeOf {α: Type} [SizeOf α] {xs ys: List α}:
  List.IsInfix xs ys ->
  sizeOf xs <= sizeOf ys := by
  intro h
  have h' := List.list_infix_def h
  obtain ⟨xs1, xs2, h'⟩ := h'
  rw [<- h']
  have hh2 := List.list_sizeOf_append (xs1 ++ xs) xs2
  have hh1 := List.list_sizeOf_prepend xs xs1
  apply Nat.le_trans hh1 hh2
