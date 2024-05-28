import SystemE
import Book.Prop13
import Book.Prop28
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_9 : ∀ (R T U W Q X S V : Point) (RT UW QX : Line),
  distinctPointsOnLine R T RT ∧
  distinctPointsOnLine U W UW ∧
  distinctPointsOnLine Q X QX ∧
  twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧
  twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧
  W.sameSide T QX ∧
  U.sameSide R QX ∧
  ∠ Q:S:R + ∠ U:V:X = ∟ + ∟ →
  ¬ RT.intersectsLine UW :=
by
  euclid_intros
  have : ∠ Q:S:R + ∠ R:S:V = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 R S Q V RT QX
    euclid_finish
  euclid_assert ∠ U:V:X = ∠ R:S:V
  euclid_apply Elements.Book1.proposition_28 W U T R X Q V S UW RT QX
  euclid_finish

end UniGeo.Parallel
