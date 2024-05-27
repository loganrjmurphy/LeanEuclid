import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_10 : ∀ (Q R S T U : Point) (QS RT QT RS : Line),
  formTriangle Q T U QT RT QS ∧
  formTriangle R S U RS QS RT ∧
  between Q U S ∧
  between R U T ∧
  ∠ R:S:Q = ∟ ∧
  ∠ S:Q:T = ∟ ∧
  |(S─U)| = |(Q─U)| →
  (△ R:S:U).congruent (△ T:Q:U) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 Q S T R U QS RT
  euclid_finish

end UniGeo.Congruent
