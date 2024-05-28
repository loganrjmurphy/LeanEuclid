import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_10 : ∀ (Q S T R U V : Point) (QS ST TQ RU UV VR : Line),
  formTriangle Q S T QS ST TQ ∧
  formTriangle R U V RU UV VR ∧
  ∠ U:R:V = ∠ S:T:Q ∧
  |(R─V)| / |(Q─T)| = |(R─U)| / |(S─T)| →
  ∠ R:U:V = ∠ Q:S:T :=
by
  euclid_intros
  euclid_assert (△ R:U:V).similar (△ T:S:Q)
  euclid_apply Triangle.similar_if (△ R:U:V) (△ T:S:Q)
  euclid_finish

end UniGeo.Triangle
