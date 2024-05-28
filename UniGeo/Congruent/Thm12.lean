import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_12 : ∀ (Q R S T U : Point) (QS RT QT RS : Line),
  formTriangle Q T U QT RT QS ∧
  formTriangle R S U RS QS RT ∧
  between Q U S ∧
  between R U T ∧
  ∠ S:Q:T = ∟ ∧
  ∠ Q:S:R = ∟ ∧
  |(Q─U)| = |(S─U)| →
  (△ Q:T:U).congruent (△ S:R:U) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 R T S Q U RT QS
  euclid_finish

end UniGeo.Congruent
