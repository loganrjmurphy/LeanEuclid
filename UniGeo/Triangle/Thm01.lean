import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_1 : ∀ (H I J K : Point) (HI IJ JH HK : Line),
  formTriangle H I J HI IJ JH ∧
  distinctPointsOnLine H K HK ∧
  IJ.intersectsLine HK ∧ K.onLine IJ ∧ between I K J ∧
  |(H─I)| = |(H─J)| ∧
  |(K─I)| = |(K─J)| →
  ∠ H:K:J = ∠ H:K:I :=
by
  euclid_intros
  euclid_assert (△ H:I:K).congruent (△ H:J:K)
  euclid_apply Triangle.congruent_if (△ H:I:K) (△ H:J:K)
  euclid_finish

end UniGeo.Triangle
