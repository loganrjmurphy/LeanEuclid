import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_15 : ∀ (Q R S T : Point) (QR ST RS QT QS : Line),
  formQuadrilateral Q R T S QR ST QT RS ∧
  distinctPointsOnLine Q S QS ∧
  ∠ S:Q:T = ∠ Q:S:R ∧
  ∠ Q:T:S = ∟ ∧
  ∠ Q:R:S = ∟ →
  |(R─S)| = |(Q─T)| :=
by
  euclid_intros
  euclid_assert (△ Q:S:T).congruent (△ S:Q:R)
  euclid_apply Triangle.congruent_if (△ Q:S:T) (△ S:Q:R)
  euclid_finish

end UniGeo.Quadrilateral
