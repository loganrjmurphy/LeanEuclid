import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_20 : ∀ (F G H I J : Point) (FH FI IG GJ JH : Line),
  formTriangle F I G FI IG FH ∧
  formTriangle G J H GJ JH FH ∧
  between F G H ∧
  I.sameSide J FH ∧
  |(F─G)| = |(H─G)| ∧
  |(G─J)| = |(F─I)| ∧
  |(G─I)| = |(H─J)| →
  ∠ G:J:H = ∠ F:I:G :=
by
  euclid_intros
  euclid_assert (△ F:G:I).congruent (△ G:H:J)
  euclid_apply Triangle.congruent_if (△ F:G:I) (△ G:H:J)
  euclid_finish

end UniGeo.Congruent
