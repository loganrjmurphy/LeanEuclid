import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Parallel

theorem theorem_1 : ∀ (S T U V W X Y Z : Point) (TV WY SZ : Line),
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧
  T.sameSide W SZ ∧
  V.sameSide Y SZ ∧
  ∠ U:X:W + ∠ T:U:X = ∟ + ∟ →
  ¬ WY.intersectsLine TV :=
by
  euclid_intros
  have : ∠S:U:T+∠T:U:X=∟ + ∟:=by
    euclid_apply proposition_13 T U S X TV SZ
    euclid_finish
  have : ∠ U:X:W + ∠ T:U:X  =  ∠S:U:T+∠T:U:X := by euclid_finish
  have : ∠ U:X:W =∠S:U:T := by euclid_finish
  have : ¬ WY.intersectsLine TV := by
    euclid_apply proposition_15 S X V T U SZ TV
    euclid_apply proposition_27' W V X U WY TV SZ
    euclid_finish
  euclid_finish

end UniGeo.Parallel
