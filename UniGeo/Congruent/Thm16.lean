import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_16 : ∀ (P Q R S T : Point) (PQ QR RS ST PT PS QS : Line),
  formTriangle P S T PS ST PT ∧
  formTriangle Q R S QR RS QS ∧
  formTriangle P Q S PQ QS PS ∧
  P.opposingSides R QS ∧ Q.sameSide R PS ∧
  Q.opposingSides T PS ∧ P.sameSide T QS ∧
  |(S─T)| = |(R─S)| ∧
  ∠ Q:R:S = ∟ ∧
  ∠ Q:S:R = ∠ P:S:T ∧
  ∠ P:T:S = ∟ →
  |(P─T)| = |(Q─R)| :=
by
  euclid_intros
  euclid_assert (△ P:S:T).congruent (△ Q:S:R)
  euclid_apply Triangle.congruent_if (△ P:S:T) (△ Q:S:R)
  euclid_finish

end UniGeo.Congruent
