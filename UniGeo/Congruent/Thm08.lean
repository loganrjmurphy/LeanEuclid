import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_8 : ∀ (P Q R S T : Point) (PQ QR RS ST PT PS QS : Line),
  formTriangle P S T PS ST PT ∧
  formTriangle Q R S QR RS QS ∧
  formTriangle P Q S PQ QS PS ∧
  P.opposingSides R QS ∧ Q.sameSide R PS ∧
  Q.opposingSides T PS ∧ P.sameSide T QS ∧
  ∠ R:Q:S = ∠ S:P:T ∧
  |(P─T)| = |(Q─R)| ∧
  |(P─Q)| = |(Q─S)| ∧
  |(Q─S)| = |(S─P)| →
  (△ P:S:T).congruent (△ Q:S:R) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Congruent
