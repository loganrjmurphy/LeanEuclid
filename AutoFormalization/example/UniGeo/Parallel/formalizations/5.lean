import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Parallel

theorem theorem_5 : ∀ (F G H V W X S T U Y R : Point) (RY SU VX FH : Line),
  distinctPointsOnLine Y R RY ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine F H FH ∧
  twoLinesIntersectAtPoint FH RY G ∧ between F G H ∧ between R T W ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W G ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between W G Y ∧
  F.sameSide V RY ∧
  V.sameSide S RY ∧
  H.sameSide X RY ∧
  X.sameSide U RY ∧
  ¬ FH.intersectsLine VX ∧
  ¬ SU.intersectsLine FH →∠ R:T:U+∠ X:W:Y = ∟ +∟ :=
by
  euclid_intros
  have : ∠X:W:Y = ∠H:G :Y := by
    euclid_apply proposition_29'''' H X Y G W FH VX RY
    euclid_finish
  have : ∠H:G:Y+∠R:T:U  = ∟ +∟:= by
    euclid_apply proposition_29'''' H U Y G T FH SU RY
    euclid_apply proposition_13 U T R Y SU RY
    euclid_finish
  euclid_finish

end UniGeo.Parallel
