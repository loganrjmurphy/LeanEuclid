import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_4 : ∀ (U V W X : Point) (UV VW WU UX : Line),
  formTriangle U V W UV VW WU ∧
  distinctPointsOnLine U X UX ∧
  VW.intersectsLine UX ∧ X.onLine VW ∧ between V X W ∧
  ∠ U:V:W = ∠ U:W:V ∧
  ∠ U:X:V = ∟ ∧ ∠ U:X:W = ∟ →
  |(U─W)| = |(U─V)| :=
by
  euclid_intros
  euclid_assert (△ U:V:X).congruent (△ U:W:X)
  euclid_apply Triangle.congruent_if (△ U:V:X) (△ U:W:X)
  euclid_finish

end UniGeo.Triangle
