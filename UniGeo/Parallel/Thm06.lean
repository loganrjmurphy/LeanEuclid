import SystemE
import Book.Prop28
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_6 : ∀ (S U V X R Y T W : Point) (SU VX RY : Line),
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧
  V.sameSide S RY ∧
  U.sameSide X RY ∧
  ∠ S:T:W + ∠ T:W:V = ∟ + ∟ →
  ¬ VX.intersectsLine SU :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_28 U S X V R Y T W SU VX RY
  euclid_finish

end UniGeo.Parallel
