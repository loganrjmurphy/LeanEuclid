import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_17 : ∀ (U W X S T V : Point) (UW WX XU ST TV VS : Line),
  formTriangle U W X UW WX XU ∧
  formTriangle S T V ST TV VS ∧
  ∠ U:X:W = ∠ T:V:S ∧
  |(W─X)| / |(S─V)| = |(U─X)| / |(T─V)| →
  ∠ U:W:X = ∠ T:S:V :=
by
  euclid_intros
  euclid_assert (△ U:W:X).similar (△ T:S:V)
  euclid_apply Triangle.similar_if (△ U:W:X) (△ T:S:V)
  euclid_finish

end UniGeo.Triangle
