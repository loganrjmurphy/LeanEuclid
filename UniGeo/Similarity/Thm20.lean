import SystemE
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_20 : ∀ (F G H I : Point) (FH FI HI GI : Line),
  formTriangle F G I FH GI FI ∧
  formTriangle G H I FH HI GI ∧
  between F G H ∧
  ∠ F:G:I = ∟ ∧ ∠ I:G:H = ∟ ∧
  ∠ H:I:F = ∟ →
  (△ F:H:I).similar (△ I:H:G) :=
by
  euclid_intros
  -- euclid_assert ∠ H:I:F = ∠ H:G:I
  euclid_finish

end UniGeo.Similarity
