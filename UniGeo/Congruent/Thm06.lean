import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_6 : ∀ (R S T U V : Point) (RT SU ST RU : Line),
  formTriangle R U V RU SU RT ∧
  formTriangle S T V ST RT SU ∧
  between R V T ∧
  between S V U ∧
  ∠ S:T:R = ∟ ∧
  |(S─T)| = |(R─U)| ∧
  ∠ U:R:T = ∟ →
  (△ S:T:V).congruent (△ U:R:V) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 R T S U V RT SU
  euclid_finish

end UniGeo.Congruent
