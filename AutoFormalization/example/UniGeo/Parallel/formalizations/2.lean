import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Parallel

theorem theorem_1 : ∀ (R S T U V W X Y : Point) (RY VX SU : Line),
  distinctPointsOnLine Y R RY  ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine S U SU ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between S T U ∧
  twoLinesIntersectAtPoint SU RY T ∧ between Y W T ∧ between W T R ∧
  V.sameSide S RY ∧
  X.sameSide U RY ∧
  ∠ S:T:W + ∠ T:W:V = ∟ + ∟ →
  ¬ VX.intersectsLine SU :=
by
  euclid_intros
  have : ∠ R:T:S + ∠ S:T:W  =  ∟ + ∟:=by
    euclid_apply proposition_13 S T R W SU RY
    euclid_finish
  have : ∠S:T:W+∠T:W:V = ∠ R:T:S + ∠ S:T:W := by euclid_finish
  have : ∠T:W:V = ∠ R:T:S  := by euclid_finish
  have : ¬ VX.intersectsLine SU := by
    euclid_apply proposition_15 R W S U T RY SU
    euclid_apply proposition_27' U V T W SU VX RY
    euclid_finish
  euclid_finish

end UniGeo.Parallel
