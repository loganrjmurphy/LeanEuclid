import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Similarity

theorem theorem_2 : ∀ (F G H I J: Point) (FI GH FG HI : Line),
  formTriangle F G J FG GH FI ∧
  formTriangle H J I GH FI HI ∧
  between H J G ∧
  between I J F ∧
  ∠ F:G:J = ∠ H:I:J →
  (△ F:G:J).similar (△ H:I:J) :=
by
  euclid_intros
  have : ∠H:J:I = ∠F:J:G := by
    euclid_apply proposition_15 F I G H J FI GH
    euclid_finish
  euclid_finish

end UniGeo.Similarity
