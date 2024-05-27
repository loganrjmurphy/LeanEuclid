import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_9 : ∀ (U W Z V X Y : Point) (UW WZ ZU VX XY YV : Line),
  formTriangle U W Z UW WZ ZU ∧
  formTriangle V X Y VX XY YV ∧
  ∠ W:U:Z = ∠ V:Y:X ∧
  ∠ U:W:Z = ∠ Y:V:X →
  |(U─W)| / |(V─Y)| = |(W─Z)| / |(V─X)| :=
by
  euclid_intros
  euclid_assert (△ U:W:Z).similar (△ Y:V:X)
  euclid_apply Triangle.similar_if (△ U:W:Z) (△ Y:V:X)
  euclid_finish

end UniGeo.Triangle
