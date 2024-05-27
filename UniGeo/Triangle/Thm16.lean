import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_16 : ∀ (F H K G I J : Point) (FH HK KF GI IJ JG : Line),
  formTriangle F H K FH HK KF ∧
  formTriangle G I J GI IJ JG ∧
  ∠ F:H:K = ∠ I:G:J ∧
  |(H─K)| / |(G─J)| = |(F─H)| / |(G─I)| →
  ∠ H:F:K = ∠ G:I:J :=
by
  euclid_intros
  euclid_assert (△ F:H:K).similar (△ I:G:J)
  euclid_apply Triangle.similar_if (△ F:H:K) (△ I:G:J)
  euclid_finish

end UniGeo.Triangle
