import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_18 : ∀ (S T V R U W : Point) (ST TV VS RU UW WR : Line),
  formTriangle S T V ST TV VS ∧
  formTriangle R U W RU UW WR ∧
  ∠ S:V:T = ∠ W:R:U ∧
  ∠ V:S:T = ∠ R:W:U →
  |(S─V)| / |(R─W)| = |(T─V)| / |(R─U)| :=
by
  euclid_intros
  euclid_assert (△ S:T:V).similar (△ W:U:R)
  euclid_apply Triangle.similar_if (△ S:T:V) (△ W:U:R)
  euclid_finish

end UniGeo.Triangle
