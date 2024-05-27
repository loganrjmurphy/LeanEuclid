import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_1 : ∀ (E F G H I : Point) (EI FH EF HI : Line),
  formTriangle E F G EF FH EI ∧
  formTriangle H I G HI EI FH ∧
  between E G I ∧
  between F G H ∧
  ∠ H:I:G = ∠ E:F:G →
  (△ G:H:I).similar (△ G:E:F) :=
by
  euclid_intros
  have : ∠ E:G:F = ∠ H:G:I := by
    euclid_apply Elements.Book1.proposition_15 E I H F G EI FH
    euclid_finish
  euclid_finish

end UniGeo.Similarity
