import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_18 : ∀ (V X Y W Z : Point) (VX VY WZ XY : Line),
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine V Y VY ∧
  distinctPointsOnLine W Z WZ ∧
  distinctPointsOnLine X Y XY ∧
  VX.intersectsLine WZ ∧ W.onLine VX ∧ between V W X ∧
  VY.intersectsLine WZ ∧ Z.onLine VY ∧ between V Z Y ∧
  VX.intersectsLine XY ∧
  VY.intersectsLine XY ∧
  ¬ XY.intersectsLine WZ ∧
  ∠ V:Y:X = ∠ W:X:Y →
  ∠ V:W:Z = ∠ V:Z:W :=
by
  euclid_intros
  have : ∠ V:Y:X = ∠ V:Z:W := by
    euclid_apply Elements.Book1.proposition_29'''' W X V Z Y WZ XY VY
    euclid_finish
  have : ∠ W:X:Y = ∠ V:W:Z := by
    euclid_apply Elements.Book1.proposition_29'''' Z Y V W X WZ XY VX
    euclid_finish
  euclid_finish

end UniGeo.Parallel
