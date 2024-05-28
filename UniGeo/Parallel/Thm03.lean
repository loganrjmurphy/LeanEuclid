import SystemE
import Book.Prop28
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_3 : ∀ (R T U W Q X S V : Point) (RT UW QX : Line),
  distinctPointsOnLine R T RT ∧
  distinctPointsOnLine U W UW ∧
  distinctPointsOnLine Q X QX ∧
  twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧
  twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧
  R.sameSide U QX ∧
  T.sameSide W QX ∧
  ∠ T:S:V + ∠ S:V:W = ∟ + ∟ →
  ¬ UW.intersectsLine RT :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_28 R T U W Q X S V RT UW QX
  euclid_finish

end UniGeo.Parallel
