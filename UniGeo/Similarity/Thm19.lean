import SystemE
import Book.Prop32
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_19 : ∀ (H I J K : Point) (HI IJ HJ IK : Line),
  formTriangle H I K HI IK HJ ∧
  formTriangle I J K IJ HJ IK ∧
  between H K J ∧
  ∠ H:K:I = ∟ ∧ ∠ I:K:J = ∟ ∧
  ∠ H:I:J = ∟ →
  (△ I:J:K).similar (△ H:I:K) :=
by
  euclid_intros
  -- euclid_assert ∠ I:K:J = ∠ H:K:I
  have : ∠ K:H:I + ∠ H:I:K = ∟ := by
    euclid_apply extend_point HJ H K as X
    euclid_apply Elements.Book1.proposition_32 I H K X HI HJ IK
    euclid_finish
  have : ∠ I:H:J + ∠ H:J:I = ∟ := by
    euclid_apply extend_point HJ H J as Y
    euclid_apply Elements.Book1.proposition_32 I H J Y HI HJ IJ
    euclid_finish
  -- euclid_assert ∠ H:I:K = ∠ H:J:I
  euclid_finish

end UniGeo.Similarity
