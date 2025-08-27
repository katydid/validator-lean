namespace List

theorem elem_lt_list [SizeOf α] {xs: List α} (h: x ∈ xs): sizeOf x ≤ sizeOf xs := by
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
