import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_13 : ∀ (U W X T V Y : Point) (UW WX XU TV VY YT : Line),
  formTriangle U W X UW WX XU ∧
  formTriangle T V Y TV VY YT ∧
  ∠ T:Y:V = ∠ W:U:X ∧
  ∠ Y:T:V = ∠ U:W:X →
  |(V─Y)| / |(U─X)| = |(T─V)| / |(W─X)| :=
by
  euclid_intros
  euclid_assert (△ T:V:Y).similar (△ W:X:U)
  euclid_apply Triangle.similar_if (△ T:V:Y) (△ W:X:U)
  euclid_finish

end UniGeo.Triangle
