import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Congruent

theorem theorem_2 : ∀ (R S T U V W : Point) (RV SV TW RT : Line),
  formTriangle W R T RV RT TW ∧
  formTriangle V S R SV RT RV ∧
  twoLinesIntersectAtPoint TW SV U ∧
  between R S T ∧
  between R W V ∧
  ∠ R:T:W = ∠ R:V:S ∧
  |(S─V)| = |(T─W)| →
  (△ R:T:W).congruent (△ R:V:S) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Congruent
