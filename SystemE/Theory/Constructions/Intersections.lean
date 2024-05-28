import SystemE.Theory.Constructions.Points

axiom intersection_lines : ∀ (L M : Line), L.intersectsLine M →
  ∃ a : Point, (a.onLine L) ∧ (a.onLine M)

axiom intersections_circle_line : ∀ (α : Circle) (L : Line), L.intersectsCircle α →
  ∃ (a b : Point), (a.onCircle α) ∧ (a.onLine L) ∧ (b.onCircle α) ∧ (b.onLine L) ∧ a ≠ b

axiom intersection_circle_line_between_points : ∀ (α : Circle) (L : Line) (b c :Point),
  (b.insideCircle α) ∧ (b.onLine L) ∧ (c.outsideCircle α) ∧ (c.onLine L) →
  ∃ a : Point, (a.onCircle α) ∧ (a.onLine L) ∧ (between b a c)

axiom intersection_circle_line_extending_points : ∀ (α : Circle) (L : Line) (b c :Point),
  (b.insideCircle α) ∧ distinctPointsOnLine b c L →
  ∃ a : Point, (a.onCircle α) ∧ (a.onLine L) ∧ (between a b c)

axiom intersection_circles : ∀ (α β : Circle), α.intersectsCircle β →
  ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β)

axiom intersection_same_side : ∀ (α β : Circle) (b c d : Point) (L : Line),
  (α.intersectsCircle β) ∧ (c.isCentre α) ∧ (d.isCentre β) ∧ (c.onLine L) ∧ (d.onLine L) ∧ ¬(b.onLine L) →
  ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β) ∧ (a.sameSide b L)

axiom intersection_opposite_side : ∀ (α β : Circle) (b c d : Point) (L : Line),
  (α.intersectsCircle β) ∧ (c.isCentre α) ∧ (d.isCentre β) ∧ (c.onLine L) ∧ (d.onLine L) ∧ ¬(b.onLine L) →
  ∃ a : Point, (a.onCircle α) ∧ (a.onCircle β) ∧ a.opposingSides b L
