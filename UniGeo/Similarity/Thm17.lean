import SystemE
import Book.Prop32
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_17 : ∀ (G H I J : Point) (GJ IJ GI HJ : Line),
  formTriangle G H J GI HJ GJ ∧
  formTriangle H I J GI IJ HJ ∧
  between G H I ∧
  ∠ G:J:I = ∟ ∧
  ∠ J:H:I = ∟ ∧ ∠ G:H:J = ∟ →
  (△ H:I:J).similar (△ H:J:G) :=
by
  euclid_intros
  -- euclid_assert ∠ I:H:J = ∠ G:H:J
  have : ∠ I:G:J + ∠ G:I:J = ∟ := by
    euclid_apply extend_point GI G I as X
    euclid_apply Elements.Book1.proposition_32 J G I X GJ GI IJ
    euclid_finish
  have : ∠ I:G:J + ∠ G:J:H = ∟ := by
    euclid_apply extend_point GJ G J as Y
    euclid_apply Elements.Book1.proposition_32 H G J Y GI GJ HJ
    euclid_finish
  -- euclid_assert ∠ G:J:H = ∠ G:I:J
  euclid_finish

end UniGeo.Similarity
