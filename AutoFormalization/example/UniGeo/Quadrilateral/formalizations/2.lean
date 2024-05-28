import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Quadrilateral

theorem theorem_2 : ∀ (V W X Y : Point) (VW WX XY VY VX : Line),
  formQuadrilateral V W Y X VX XY VY WX ∧
  distinctPointsOnLine V X VX ∧
  ∠ V:W:X=∟ ∧ ∠ V:Y:X = ∟ ∧ ∠ X:V:Y = ∠ V:X:W →
  |(X─Y)| = |(V─W)| :=
by
  euclid_intros
  have : ∠ V:W:X = ∠ V:Y:X := by euclid_finish
  have : △ V:X:Y ≅ △ X:V:W := by euclid_finish
  have : |(X─Y)| = |(V─W)|:= by
    euclid_apply (△ V:X:Y).congruent_if △ X:V:W
    euclid_finish
  euclid_finish

end UniGeo.Quadrilateral
