import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_12 : ∀ (I J K F G H : Point) (IJ JK KI FG GH HF : Line),
  formTriangle I J K IJ JK KI ∧
  formTriangle F G H FG GH HF ∧
  ∠ J:I:K = ∠ H:F:G ∧
  ∠ I:K:J = ∠ F:G:H →
  |(I─K)| / |(F─G)| = |(J─K)| / |(G─H)| :=
by
  euclid_intros
  euclid_assert (△ I:J:K).similar (△ F:H:G)
  euclid_apply (△ I:J:K).similar_if (△ F:H:G)
  euclid_finish

end UniGeo.Triangle
