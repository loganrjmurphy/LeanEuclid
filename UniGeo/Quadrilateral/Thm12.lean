import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_12 : ∀ (T U V W : Point) (TU VW UV TW TV : Line),
  formQuadrilateral T U W V TU VW TW UV ∧
  distinctPointsOnLine T V TV ∧
  ∠ T:V:U = ∠ V:T:W ∧
  ∠ T:U:V = ∟ ∧
  ∠ V:W:T = ∟ →
  |(T─U)| = |(V─W)| :=
by
  euclid_intros
  euclid_assert (△ T:V:W).congruent (△ V:T:U)
  euclid_apply Triangle.congruent_if (△ T:V:W) (△ V:T:U)
  euclid_finish

end UniGeo.Quadrilateral
