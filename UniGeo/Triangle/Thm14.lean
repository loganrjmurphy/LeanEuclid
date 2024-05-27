import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_14 : ∀ (I G H F J K : Point) (IG GH HI FJ JK KF : Line),
  formTriangle I G H IG GH HI ∧
  formTriangle F J K FJ JK KF ∧
  ∠ G:I:H = ∠ J:K:F ∧
  ∠ G:H:I = ∠ J:F:K →
  |(G─I)| / |(J─K)| = |(G─H)| / |(F─J)| :=
by
  euclid_intros
  euclid_assert (△ G:H:I).similar (△ J:F:K)
  euclid_apply Triangle.similar_if (△ G:H:I) (△ J:F:K)
  euclid_finish

end UniGeo.Triangle
