import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Congruent

theorem theorem_5 : ∀ (S T U V : Point) (ST TU UV SV SU : Line),
  formTriangle S U V SU UV SV ∧
  formTriangle S T U ST TU SU ∧
  T.opposingSides V SU ∧
  |(S─T)| = |(U─V)| ∧
  ¬ UV.intersectsLine ST →
  |(S─V)| = |(T─U)| :=
by
  euclid_intros
  have : ∠S:U:V = ∠T:S:U :=by
    euclid_apply proposition_29''' T V S U ST UV SU
    euclid_finish
  have : △S:T:U≅△U:V:S := by euclid_finish
  have : |(S─V)| = |(T─U)| := by
    euclid_apply (△S:T:U).congruent_if △U:V:S
    euclid_finish
  euclid_finish

end UniGeo.Congruent
