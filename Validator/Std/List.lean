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
