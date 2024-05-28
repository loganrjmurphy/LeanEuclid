import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_19 : ∀ (P R T V W Y S Z Q U X : Point) (PR TV WY SZ : Line),
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
  ¬ PR.intersectsLine TV ∧
  ¬ WY.intersectsLine PR →
  (∠ S:X:W) = (∠ V:U:Z) :=
by
  euclid_intros
  have : ∠ V:U:Z = ∠ R:Q:Z := by
    euclid_apply Elements.Book1.proposition_29'''' V R Z U Q TV PR SZ
    euclid_finish
  have : ∠ R:Q:Z = ∠ S:X:W := by
    euclid_apply Elements.Book1.proposition_29''' R W Q X PR WY SZ
    euclid_finish
  euclid_finish

end UniGeo.Parallel
