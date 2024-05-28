import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_13 : ∀ (H I J K : Point) (HI JK IJ HK HJ : Line),
  formQuadrilateral H I K J HI JK HK IJ ∧
  distinctPointsOnLine H J HJ ∧
  |(J─K)| = |(H─I)| ∧
  |(H─K)| = |(I─J)| →
  ∠ H:K:J = ∠ H:I:J :=
by
  euclid_intros
  euclid_assert (△ H:I:J).congruent (△ J:K:H)
  euclid_apply Triangle.congruent_if (△ H:I:J) (△ J:K:H)
  euclid_finish

end UniGeo.Quadrilateral
