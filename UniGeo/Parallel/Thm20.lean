import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_20 : ∀ (W X V Y Z : Point) (WX VY VX WY : Line),
  distinctPointsOnLine W X WX ∧
  distinctPointsOnLine V Y VY ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine W Y WY ∧
  twoLinesIntersectAtPoint VX WY Z ∧ between W Z X ∧ between W Z Y ∧
  (∠ Y:V:Z) = (∠ V:Y:Z) ∧
  ¬ WX.intersectsLine VY →
  (∠ X:W:Z) = (∠ W:X:Z) :=
by
  euclid_intros
  have : ∠ Y:V:Z = ∠ W:X:Z := by
    euclid_apply Elements.Book1.proposition_29''' W Y X V WX VY VX
    euclid_finish
  have : ∠ X:W:Z = ∠ V:Y:Z := by
    euclid_apply Elements.Book1.proposition_29''' X V W Y WX VY WY
    euclid_finish
  euclid_finish

end UniGeo.Parallel
