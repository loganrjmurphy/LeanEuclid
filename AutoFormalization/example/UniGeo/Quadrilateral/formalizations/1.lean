import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Quadrilateral

theorem theorem_1 : ∀ (T U V W : Point) (TU UV VW TW TV : Line),
  formQuadrilateral T U W V TU VW TW UV ∧
  distinctPointsOnLine T V TV ∧
  ∠ U:T:V = ∠ T:V:W ∧∠ V:T:W = ∠ T:V:U →
  |(T─W)| = |(U─V)|:=
by
  euclid_intros
  have : △T:U:V≅△V:W:T := by euclid_finish
  have : |(T─W)| = |(U─V)|:= by
    euclid_apply (△T:U:V).congruent_if △V:W:T
    euclid_finish
  euclid_finish

end UniGeo.Quadrilateral
