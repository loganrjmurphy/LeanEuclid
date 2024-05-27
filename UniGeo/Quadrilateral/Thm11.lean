import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_11 : ∀ (S T U V : Point) (ST UV TU SV SU : Line),
  formQuadrilateral S T V U ST UV SV TU ∧
  distinctPointsOnLine S U SU ∧
  |(U─V)| = |(T─U)| ∧
  |(S─T)| = |(S─V)| →
  ∠ S:V:U = ∠ S:T:U :=
by
  euclid_intros
  euclid_assert (△ S:T:U).congruent (△ S:V:U)
  euclid_apply Triangle.congruent_if (△ S:T:U) (△ S:V:U)
  euclid_finish

end UniGeo.Quadrilateral
