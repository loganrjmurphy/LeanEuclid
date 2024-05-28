import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_10 : ∀ (V Y W X Z : Point) (VY WX WY VX : Line),
  distinctPointsOnLine V Y VY ∧
  distinctPointsOnLine W X WX ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine V X VX ∧
  twoLinesIntersectAtPoint WY VX Z ∧ between W Z Y ∧ between V Z X ∧
  ¬ WX.intersectsLine VY ∧
  ∠ Y:V:Z = ∠ Z:Y:V →
  ∠ X:W:Z = ∠ W:X:Z :=
by
  euclid_intros
  have : ∠ Y:V:Z= ∠ W:X:Z := by
    euclid_apply Elements.Book1.proposition_29''' W Y X V WX VY VX
    euclid_finish
  have : ∠ X:W:Z = ∠ V:Y:Z := by
    euclid_apply Elements.Book1.proposition_29''' V X Y W VY WX WY
    euclid_finish
  euclid_finish

end UniGeo.Parallel
