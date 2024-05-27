import SystemE
import Book.Prop15
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_5 : ∀ (F G H I J : Point) (FI GH FH GI : Line),
  formTriangle F I J FI GI FH ∧
  formTriangle G H J GH FH GI ∧
  between F J H ∧
  between G J I ∧
  ¬ FI.intersectsLine GH →
  (△ F:I:J).similar (△ H:G:J) :=
by
  euclid_intros
  have : ∠ G:J:H = ∠ F:J:I := by
    euclid_apply Elements.Book1.proposition_15 G I H F J GI FH
    euclid_finish
  have : ∠ J:F:I = ∠ G:H:J := by
    euclid_apply Elements.Book1.proposition_29''' G I H F GH FI FH
    euclid_finish
  euclid_finish

end UniGeo.Similarity
