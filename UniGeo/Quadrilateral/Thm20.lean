import SystemE
import Book.Prop28
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_20 : ∀ (Q R S T U : Point) (QR ST RS QT QS RT : Line),
  formQuadrilateral Q R T S QR ST QT RS ∧
  distinctPointsOnLine Q S QS ∧
  distinctPointsOnLine R T RT ∧
  twoLinesIntersectAtPoint QS RT U ∧
  ∠ Q:T:S = ∠ Q:R:S ∧
  ∠ R:S:T = ∠ R:Q:T →
  ¬ QT.intersectsLine RS :=
by
  euclid_intros
  have : ∠ R:Q:T + ∠ Q:R:S + ∠ R:S:T + ∠ Q:T:S = ∟ + ∟ + ∟ + ∟ := by
    euclid_apply quadrilateralAnglesSum Q R T S QR ST QT RS
    euclid_finish
  euclid_assert ∠ R:Q:T + ∠ Q:R:S = ∟ + ∟

  euclid_apply extend_point QT T Q as W
  euclid_apply extend_point RS S R as X
  euclid_apply extend_point QR Q R as Y
  euclid_apply extend_point QR R Q as Z

  euclid_apply Elements.Book1.proposition_28 W T X S Z Y Q R QT RS QR
  euclid_finish

end UniGeo.Quadrilateral
