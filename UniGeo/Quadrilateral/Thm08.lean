import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_8 : ∀ (V W X Y : Point) (VW XY WX VY VX : Line),
  formQuadrilateral V W Y X VW XY VY WX ∧
  distinctPointsOnLine V X VX ∧
  ∠ X:Y:V = ∟ ∧
  ¬ VW.intersectsLine XY ∧
  ∠ V:W:X = ∟ →
  |(V─Y)| = |(W─X)| :=
by
  euclid_intros
  have : ∠ W:V:X = ∠ V:X:Y := by
    euclid_apply Elements.Book1.proposition_29''' W Y V X VW XY VX
    euclid_finish
  euclid_assert (△ V:X:Y).congruent (△ X:V:W)
  euclid_apply Triangle.congruent_if (△ V:X:Y) (△ X:V:W)
  euclid_finish

end UniGeo.Quadrilateral
