import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_14 : ∀ (H J W Y T V S Z I X U : Point) (HJ WY TV SZ : Line),
  distinctPointsOnLine H J HJ ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint HJ SZ I ∧ between H I J ∧ between S U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X I ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between X I Z ∧
  V.sameSide Y SZ ∧
  Y.sameSide J SZ ∧
  T.sameSide W SZ ∧
  W.sameSide H SZ ∧
  ¬ HJ.intersectsLine WY ∧
  ¬ TV.intersectsLine HJ →
  ∠ S:X:Y = ∠ T:U:Z :=
by
  euclid_intros
  have : ∠ S:X:Y = ∠ J:I:S := by
    euclid_apply Elements.Book1.proposition_29'''' Y J S X I WY HJ SZ
    euclid_finish
  have : ∠ J:I:S = ∠ T:U:Z := by
    euclid_apply Elements.Book1.proposition_29''' J T I U HJ TV SZ
    euclid_finish
  euclid_finish

end UniGeo.Parallel
