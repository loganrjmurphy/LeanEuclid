import SystemE.Theory.Sorts
import SystemE.Theory.Relations


axiom arbitrary_point :
  ∃ _ : Point, true

axiom distinct_points :
  ∀ p₁ : Point, ∃ p₂ : Point, p₁ ≠ p₂

axiom line_nonempty :
  ∀ l : Line, ∃ p : Point, p.onLine l

axiom exists_distincts_points_on_line :
  ∀ l : Line, ∀ p : Point, ∃ p' : Point, p ≠ p' ∧ p'.onLine l

axiom exists_point_between_points_on_line :
  ∀ (L : Line) (b c : Point), distinctPointsOnLine b c L
  → ∃ a : Point, (a.onLine L) ∧ (between b a c)

axiom exists_point_between_points_not_on_line :
  ∀ (L M : Line) (b c : Point), distinctPointsOnLine b c L ∧ L ≠ M
  → ∃ a : Point, (a.onLine L) ∧ (between b a c) ∧ ¬(a.onLine M)

/--
This rule is not in [Avigad et al., 2009] but is convenient for proving some propositions.
-/
axiom point_between_points_shorter_than : ∀ (L : Line) (b c : Point) (s : Segment),
  distinctPointsOnLine b c L ∧ (|s| > 0) →
  ∃ a : Point, (a.onLine L) ∧ (between b a c) ∧ |(b─a)| < |s|

axiom extend_point :
  ∀ (L : Line) (b c : Point), distinctPointsOnLine b c L
  → ∃ a : Point, (a.onLine L) ∧ (between b c a)

axiom extend_point_not_on_line :
  ∀ (L M : Line) (b c : Point), distinctPointsOnLine b c L ∧ L ≠ M
  → ∃ a : Point, (a.onLine L) ∧ (between b c a) ∧ ¬(a.onLine M)

/--
This rule is not in [Avigad et al., 2009] but is convenient for proving some propositions.
-/
axiom extend_point_longer :
  ∀ (L : Line) (b c : Point) (s : Segment), distinctPointsOnLine b c L
  → ∃ a : Point, (a.onLine L) ∧ (between b c a) ∧ |(c─a)| > |s|

axiom point_same_side :
  ∀ (L : Line) (b : Point), ¬(b.onLine L) → ∃ a : Point, a.sameSide b L

axiom distinct_point_same_side:
  ∀ (L : Line) (b c : Point), ¬(b.onLine L) → ∃ a : Point, a ≠ c ∧ a.sameSide b L

/--
A stronger version of the Points construction rule 6 in [Avigad et al., 2009], which is convenient for proving some propositions.
-/
axiom point_on_line_same_side :
  ∀ (L M : Line) (b : Point), ¬(b.onLine L) ∧ (L.intersectsLine M)
  → ∃ a : Point, a.onLine M ∧ a.sameSide b L

axiom exists_point_opposite :
  ∀ (L : Line) (b : Point), ¬(b.onLine L) → ∃ a : Point, a.opposingSides b L

axiom exists_distinct_point_opposite_side :
  ∀ (L : Line) (b c : Point), ¬(b.onLine L) → ∃ a : Point, a ≠ c ∧ a.opposingSides b L

axiom exists_point_on_circle :
  ∀ (α : Circle), ∃ a : Point, a.onCircle α

axiom exists_distinct_point_on_circle :
  ∀ (α : Circle) (b : Point), ∃ a : Point, a ≠ b ∧ (a.onCircle α)

axiom exists_point_inside_circle :
  ∀ (α : Circle), ∃ a : Point, a.insideCircle α

axiom exists_distinct_point_inside_circle :
  ∀ (α : Circle) (b : Point), ∃ a : Point, a ≠ b ∧ a.insideCircle α

axiom exists_point_outside_circle :
  ∀ (α : Circle), ∃ a : Point, a.outsideCircle α

axiom exists_distinct_point_outside_circle :
  ∀ (α : Circle) (b : Point),  ∃ a : Point, a ≠ b ∧ a.outsideCircle α
