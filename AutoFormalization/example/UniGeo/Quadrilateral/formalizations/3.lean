import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Quadrilateral

theorem theorem_3 : ∀ (U V W S T : Point) (UV TV SV TU ST SU : Line),
  formQuadrilateral U V T S UV ST TU SV ∧
  distinctPointsOnLine V T TV ∧
  distinctPointsOnLine S U SU ∧
  twoLinesIntersectAtPoint TV SU W ∧
  |(S─T)| = |(T─U)| ∧ |(S─V)| = |(U─V)|→
  |(U─W)| = |(S─W)| :=
by
  euclid_intros
  have : △S:T:V≅△U:T:V := by euclid_finish
  have : ∠S:T:V = ∠U:T:V := by
    euclid_apply (△S:T:V).congruent_if △U:T:V
    euclid_finish
  euclid_assert |(T─W)| = |(T─W)|
  have : △S:T:W≅△U:T:W := by euclid_finish
  have : |(U─W)| = |(S─W)| := by
    euclid_apply (△S:T:W).congruent_if △U:T:W
    euclid_finish
  euclid_finish

end UniGeo.Quadrilateral
