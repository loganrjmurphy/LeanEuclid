import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_7 : ∀ (E F G H I : Point) (EF HI EI FH : Line),
  formTriangle E F G EF FH EI ∧
  formTriangle H I G HI EI FH ∧
  between E G I ∧
  between F G H ∧
  |(F─G)| / |(G─H)| = |(E─G)| / |(G─I)| →
  (△ E:F:G).similar (△ I:H:G) :=
by
  euclid_intros
  have : ∠ H:G:I = ∠ E:G:F := by
    euclid_apply Elements.Book1.proposition_15 E I H F G EI FH
    euclid_finish
  euclid_finish

end UniGeo.Similarity
