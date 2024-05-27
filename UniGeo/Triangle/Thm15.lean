import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_15 : ∀ (S T V Q R U : Point) (ST TV VS QR RU UQ : Line),
  formTriangle S T V ST TV VS ∧
  formTriangle Q R U QR RU UQ ∧
  ∠ T:S:V = ∠ R:U:Q ∧
  |(S─V)| / |(Q─U)| = |(S─T)| / |(R─U)| →
  ∠ S:T:V = ∠ Q:R:U :=
by
  euclid_intros
  euclid_assert (△ S:T:V).similar (△ U:R:Q)
  euclid_apply Triangle.similar_if (△ S:T:V) (△ U:R:Q)
  euclid_finish

end UniGeo.Triangle
