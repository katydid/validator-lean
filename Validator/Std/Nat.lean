namespace Nat

theorem nat_min (x y: Nat):
  min x y = if x ≤ y then x else y := by
  rfl
