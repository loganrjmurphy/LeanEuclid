import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Congruent

theorem theorem_3 : ∀ (S T U V W : Point) (TU SV TV SU : Line),
  formTriangle S V W SV TV SU ∧
  formTriangle U T W TU TV SU ∧
  between U W S ∧
  between T W V ∧
  ¬ TU.intersectsLine SV ∧
  |(T─U)| = |(S─V)| →
  (△ S:V:W).congruent (△ U:T:W) :=
by
  euclid_intros
  have :  ∠S:W:V = ∠T:W:U := by
    euclid_apply proposition_15 T V U S W TV SU
    euclid_finish
  have :  ∠ W:V:S= ∠ U:T:W := by
    euclid_apply proposition_29''' U S T V TU SV TV
    euclid_finish
  euclid_finish

end UniGeo.Congruent
