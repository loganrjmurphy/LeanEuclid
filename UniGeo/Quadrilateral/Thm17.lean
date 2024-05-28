import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_17 : ∀ (P Q R S : Point) (PQ RS QR PS PR : Line),
  formQuadrilateral P Q S R PQ RS PS QR ∧
  distinctPointsOnLine P R PR ∧
  ∠ Q:P:R = ∠ S:P:R ∧
  ∠ P:R:Q = ∠ P:R:S →
  |(R─S)| = |(Q─R)| :=
by
  euclid_intros
  euclid_assert (△ P:Q:R).congruent (△ P:S:R)
  euclid_apply Triangle.congruent_if (△ P:Q:R) (△ P:S:R)
  euclid_finish

end UniGeo.Quadrilateral
