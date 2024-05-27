import SystemE
import Book.Prop28
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_8 : ∀ (T V W Y S Z U X : Point) (TV WY SZ : Line),
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧
  T.sameSide W SZ ∧
  V.sameSide Y SZ ∧
  ∠ V:U:X + ∠ U:X:Y = ∟ + ∟ →
  ¬ TV.intersectsLine WY :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_28 T V W Y S Z U X TV WY SZ
  euclid_finish

end UniGeo.Parallel
