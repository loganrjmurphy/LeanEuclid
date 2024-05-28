import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_19 : ∀ (V W X S U T : Point) (VW WX XV SU UT TS : Line),
  formTriangle V W X VW WX XV ∧
  formTriangle S U T SU UT TS ∧
  ∠ W:V:X = ∠ U:S:T ∧
  ∠ V:W:X = ∠ S:U:T →
  |(W─X)| / |(T─U)| = |(V─X)| / |(S─T)| :=
by
  euclid_intros
  euclid_assert (△ V:W:X).similar (△ S:U:T)
  euclid_apply Triangle.similar_if (△ V:W:X) (△ S:U:T)
  euclid_finish

end UniGeo.Triangle
