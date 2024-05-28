import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_3 : ∀ (P Q R S T : Point) (PS ST PT RS RT : Line),
  formTriangle P S T PS ST PT ∧
  formTriangle R S T RS ST RT ∧
  P.sameSide R ST ∧
  twoLinesIntersectAtPoint PS RT Q ∧
  ∠ S:P:T = ∠ T:R:S ∧
  ∠ R:S:T = ∟ ∧
  ∠ P:T:S = ∟ →
  (△ R:S:T).congruent (△ P:T:S) :=
by
  euclid_intros
  euclid_assert ∠ P:T:S = ∠ R:S:T
  euclid_finish

end UniGeo.Congruent
