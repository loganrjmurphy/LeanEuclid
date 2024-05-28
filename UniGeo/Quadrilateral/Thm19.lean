import SystemE
import Book.Prop05
import Book.Prop29
import Book.Prop34
import UniGeo.Relations
-- needed for some reason, for now
set_option maxHeartbeats 350000
namespace UniGeo.Quadrilateral

theorem theorem_19 : ∀ (U V W X Y : Point) (UV WX VW UX UW VX UY XY : Line),
  formQuadrilateral U V X W UV WX UX VW ∧
  distinctPointsOnLine U W UW ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine U Y UY ∧
  distinctPointsOnLine X Y XY ∧
  Y.opposingSides W UX ∧
  ¬ UY.intersectsLine VX ∧
  ¬ WX.intersectsLine UV ∧
  ¬ XY.intersectsLine UV ∧
  |(V─X)| = |(U─W)| →
  ∠ V:W:X = ∠ U:X:W :=
by
  euclid_intros
  have : |(V─X)| = |(U─Y)| := by
    euclid_apply Elements.Book1.proposition_34' U V Y X UV XY UY VX
    euclid_finish

  euclid_assert |(U─Y)| = |(U─W)|

  have : ∠ U:W:Y = ∠ U:Y:W := by
    euclid_apply Elements.Book1.proposition_5' U W Y UW XY UY
    euclid_finish

  have : ∠ V:X:W = ∠ U:Y:X := by
    euclid_apply Elements.Book1.proposition_29'''' V U W X Y VX UY WX
    euclid_finish

  euclid_assert ∠ V:X:W = ∠ U:W:Y
  euclid_assert (△ U:W:X).congruent (△ V:X:W)
  euclid_apply Triangle.congruent_if (△ U:W:X) (△ V:X:W)
  euclid_finish

end UniGeo.Quadrilateral
