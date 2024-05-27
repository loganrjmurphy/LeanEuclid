import SystemE
import Book.Prop28
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_12 : ∀ (P R T V W Y S Z Q U X : Point) (PR TV WY SZ : Line),
  distinctPointsOnLine P R PR ∧
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint PR SZ Q ∧ between P Q R ∧ between S Q U ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between Q U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧
  R.sameSide V SZ ∧
  V.sameSide Y SZ ∧
  P.sameSide T SZ ∧
  T.sameSide W SZ ∧
  ¬ WY.intersectsLine PR ∧
  ¬ TV.intersectsLine PR →
  ¬ WY.intersectsLine TV :=
by
  euclid_intros
  have : ∠ S:U:T = ∠ P:Q:S := by
    euclid_apply Elements.Book1.proposition_29'''' P T S Q U PR TV SZ
    euclid_finish
  have : ∠ P:Q:S = ∠ S:X:W := by
    euclid_apply Elements.Book1.proposition_29'''' P W S Q X PR WY SZ
    euclid_finish
  euclid_assert ∠ S:U:T = ∠ S:X:W
  euclid_apply Elements.Book1.proposition_28 V T Y W S Z U X TV WY SZ
  euclid_finish

end UniGeo.Parallel
