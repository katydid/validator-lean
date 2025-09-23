namespace Lex

theorem lex_sizeOf [SizeOf α] [SizeOf β]
  (x1 x2: α)
  (y1 y2: β)
  (hx: x1 = x2 \/ sizeOf x1 < sizeOf x2)
  (hy: sizeOf y1 < sizeOf y2)
  :Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x1, y1)
    (x2, y2) := by
  rw [Prod.lex_def]
  simp only
  cases hx
  · apply Or.inr
    apply And.intro
    assumption
    assumption
  · apply Or.inl
    assumption
