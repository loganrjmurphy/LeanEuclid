import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_15 : ∀ (S T U V : Point) (ST TU UV SV SU : Line),
  formTriangle S T U ST TU SU ∧
  formTriangle S U V SU UV SV ∧
  V.opposingSides T SU ∧
  ∠ U:V:S = ∟ ∧
  ∠ U:S:V = ∠ S:U:T ∧
  ∠ S:T:U = ∟ →
  |(U─V)| = |(S─T)| :=
by
  euclid_intros
  euclid_assert (△ S:U:V).congruent (△ U:S:T)
  euclid_apply Triangle.congruent_if (△ S:U:V) (△ U:S:T)
  euclid_finish

end UniGeo.Congruent
