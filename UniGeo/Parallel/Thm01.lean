import SystemE
import Book.Prop13
import Book.Prop28
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_1 : ∀ (T V W Y S Z U X : Point) (TV WY SZ : Line),
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧
  T.sameSide W SZ ∧
  V.sameSide Y SZ ∧
  ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ →
  ¬ WY.intersectsLine TV :=
by
  euclid_intros
  have : ∠ S:U:T + ∠ T:U:X = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 T U S X TV SZ
    euclid_finish
  euclid_assert ∠ W:X:Z = ∠ T:U:X
  euclid_apply Elements.Book1.proposition_28 Y W V T Z S X U WY TV SZ
  euclid_finish

end UniGeo.Parallel
