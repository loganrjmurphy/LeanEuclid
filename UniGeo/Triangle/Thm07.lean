import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_7 : ∀ (T W Y U V X : Point) (TW WY YT UV VX XU : Line),
  formTriangle T W Y TW WY YT ∧
  formTriangle U V X UV VX XU ∧
  ∠ W:T:Y = ∠ U:V:X ∧
  |(T─Y)| / |(U─V)| = |(T─W)| / |(V─X)| →
  ∠ T:W:Y = ∠ U:X:V :=
by
  euclid_intros
  euclid_assert (△ T:W:Y).similar (△ V:X:U)
  euclid_apply Triangle.similar_if (△ T:W:Y) (△ V:X:U)
  euclid_finish

end UniGeo.Triangle
