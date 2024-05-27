import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_14 : ∀ (U V W X Y : Point) (UW VX UX VW : Line),
  formTriangle U X Y UX VX UW ∧
  formTriangle V W Y VW UW VX ∧
  between U Y W ∧
  between V Y X ∧
  |(U─Y)| = |(W─Y)| ∧
  |(U─X)| = |(V─W)| ∧
  |(X─Y)| = |(V─Y)| →
  ∠ V:W:Y = ∠ X:U:Y :=
by
  euclid_intros
  euclid_assert (△ U:X:Y).congruent (△ W:V:Y)
  euclid_apply Triangle.congruent_if (△ U:X:Y) (△ W:V:Y)
  euclid_finish

end UniGeo.Congruent
