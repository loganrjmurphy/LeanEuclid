import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_5 : ∀ (P Q R S T U : Point) (PR PT QT RU : Line),
  formTriangle P R U PR RU PT ∧
  formTriangle P Q T PR QT PT ∧
  twoLinesIntersectAtPoint QT RU S ∧
  between P Q R ∧
  between P U T ∧
  ∠ P:R:U = ∠ P:T:Q ∧
  |(Q─T)| = |(R─U)| →
  (△ P:R:U).congruent (△ P:T:Q) :=
by
  euclid_intros
  euclid_assert ∠ U:P:R = ∠ Q:P:T
  euclid_finish

end UniGeo.Congruent
