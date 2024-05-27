import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_17 : ∀ (R S T U V : Point) (RT SU ST RU : Line),
  formTriangle R U V RU SU RT ∧
  formTriangle S T V ST RT SU ∧
  between R V T ∧
  between S V U ∧
  |(U─V)| = |(T─V)| ∧
  |(S─V)| = |(R─V)| →
  |(R─U)| = |(S─T)| :=
by
  euclid_intros
  have : ∠ R:V:U = ∠ S:V:T := by
    euclid_apply Elements.Book1.proposition_15 R T U S V RT SU
    euclid_finish
  euclid_assert (△ R:U:V).congruent (△ S:T:V)
  euclid_apply Triangle.congruent_if (△ R:U:V) (△ S:T:V)
  euclid_finish

end UniGeo.Congruent
