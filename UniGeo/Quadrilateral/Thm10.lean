import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_10 : ∀ (T U V W : Point) (TU VW UV TW TV : Line),
  formQuadrilateral T U W V TU VW TW UV ∧
  distinctPointsOnLine T V TV ∧
  ¬ TU.intersectsLine VW ∧
  |(V─W)| = |(T─U)| →
  ∠ V:T:W = ∠ T:V:U :=
by
  euclid_intros
  have : ∠ T:V:W = ∠ U:T:V := by
    euclid_apply Elements.Book1.proposition_29''' W U V T VW TU TV
    euclid_finish
  euclid_assert (△ T:U:V).congruent (△ V:W:T)
  euclid_apply Triangle.congruent_if (△ T:U:V) (△ V:W:T)
  euclid_finish

end UniGeo.Quadrilateral
