import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_11 : ∀ (V W X T U Y : Point) (VW WX XV TU UY YT : Line),
  formTriangle V W X VW WX XV ∧
  formTriangle T U Y TU UY YT ∧
  ∠ X:V:W = ∠ U:T:Y ∧
  ∠ V:W:X = ∠ T:Y:U →
  |(W─X)| / |(U─Y)| = |(V─W)| / |(T─Y)| :=
by
  euclid_intros
  euclid_assert (△ V:W:X).similar (△ T:Y:U)
  euclid_apply Triangle.similar_if (△ V:W:X) (△ T:Y:U)
  euclid_finish

end UniGeo.Triangle
