import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_7 : ∀ (S U V X R Y T W : Point) (SU VX RY : Line),
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧
  U.sameSide X RY ∧
  V.sameSide S RY ∧
  ¬ VX.intersectsLine SU →
  ∠ T:W:X = ∠ S:T:W :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29 S U V X R Y T W SU VX RY
  euclid_finish

end UniGeo.Parallel
