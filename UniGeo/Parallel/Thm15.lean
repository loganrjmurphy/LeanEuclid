import SystemE
import Book.Prop13
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_15 : ∀ (G I S U V X R Y H T W : Point) (GI SU VX RY : Line),
  distinctPointsOnLine G I GI ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint GI RY H ∧ between G H I ∧ between R H T ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between H T W ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧
  G.sameSide S RY ∧
  S.sameSide V RY ∧
  I.sameSide U RY ∧
  U.sameSide X RY ∧
  ¬ VX.intersectsLine GI ∧
  ¬ GI.intersectsLine SU →
  ∠ X:W:Y + ∠ R:T:U = ∟ + ∟ :=
by
  euclid_intros
  have : ∠ R:T:U = ∠ I:H:R := by
    euclid_apply Elements.Book1.proposition_29'''' I U R H T GI SU RY
    euclid_finish
  have : ∠ I:H:R + ∠ X:W:Y = ∟ + ∟:= by
    euclid_apply Elements.Book1.proposition_29'''' I X R H W GI VX RY
    euclid_apply Elements.Book1.proposition_13 X W Y R VX RY
    euclid_finish
  euclid_finish

end UniGeo.Parallel
