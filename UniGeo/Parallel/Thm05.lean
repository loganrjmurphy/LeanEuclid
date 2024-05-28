import SystemE
import Book.Prop13
import Book.Prop28
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_5 : ∀ (S U V X R Y T W : Point) (SU VX RY : Line),
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between T W Y ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between R T W ∧
  V.sameSide S RY ∧
  X.sameSide U RY ∧
  ∠ R:T:S + ∠ V:W:Y = ∟ + ∟ →
  ¬ VX.intersectsLine SU :=
by
  euclid_intros
  have : ∠ R:T:S + ∠ S:T:W = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 S T R W SU RY
    euclid_finish
  euclid_assert ∠ V:W:Y = ∠ S:T:W
  euclid_apply Elements.Book1.proposition_28 X V U S Y R W T VX SU RY
  euclid_finish

end UniGeo.Parallel
