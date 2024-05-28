import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_2 : ∀ (R S T U : Point) (RS ST TR RU : Line),
  formTriangle R S T RS ST TR ∧
  distinctPointsOnLine R U RU ∧
  ST.intersectsLine RU ∧ U.onLine ST ∧ between S U T ∧
  |(S─U)| = |(T─U)| ∧
  ∠ R:U:S = ∟ ∧ ∠ R:U:T = ∟ →
  ∠ T:R:U = ∠ S:R:U :=
by
  euclid_intros
  euclid_assert (△ R:S:U).congruent (△ R:T:U)
  euclid_apply Triangle.congruent_if (△ R:S:U) (△ R:T:U)
  euclid_finish

end UniGeo.Triangle
