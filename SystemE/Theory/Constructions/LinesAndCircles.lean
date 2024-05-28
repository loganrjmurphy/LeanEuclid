import SystemE.Theory.Relations

axiom line_from_points : ∀ (a b : Point), a ≠ b →
  ∃ L : Line, (a.onLine L) ∧ (b.onLine L)

axiom circle_from_points : ∀ (a b : Point), a ≠ b →
  ∃ α : Circle, (a.isCentre α) ∧ (b.onCircle α)
