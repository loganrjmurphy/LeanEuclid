import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_4 : ∀ (E F G H I : Point) (EF GH EG FH : Line),
  formTriangle E F I EF FH EG ∧
  formTriangle G H I GH FH EG ∧
  between E I G ∧
  between H I F ∧
  ∠ H:G:I = ∠ F:E:I →
  (△ G:H:I).similar (△ E:F:I) :=
by
  euclid_intros
  have : ∠ E:I:F = ∠ G:I:H := by
    euclid_apply Elements.Book1.proposition_15 E G H F I EG FH
    euclid_finish
  euclid_finish

end UniGeo.Similarity
