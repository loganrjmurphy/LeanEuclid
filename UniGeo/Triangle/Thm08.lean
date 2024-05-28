import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_8 : ∀ (U X Y V W Z : Point) (UX XY YU VW WZ ZV : Line),
  formTriangle U X Y UX XY YU ∧
  formTriangle V W Z VW WZ ZV ∧
  ∠ V:Z:W = ∠ X:U:Y ∧
  |(V─Z)| / |(U─X)| = |(W─Z)| / |(U─Y)| →
  ∠ V:W:Z = ∠ U:Y:X :=
by
  euclid_intros
  euclid_assert (△ V:W:Z).similar (△ X:Y:U)
  euclid_apply Triangle.similar_if (△ V:W:Z) (△ X:Y:U)
  euclid_finish

end UniGeo.Triangle
