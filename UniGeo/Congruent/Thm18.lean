import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_18 : ∀ (E F G H I : Point) (EG FH EH FG : Line),
  formTriangle E H I EH FH EG ∧
  formTriangle F G I FG EG FH ∧
  between E I G ∧
  between F I H ∧
  |(E─I)| = |(G─I)| ∧
  ¬ EH.intersectsLine FG →
  |(H─I)| = |(F─I)| :=
by
  euclid_intros
  have : ∠ I:E:H = ∠ I:G:F := by
    euclid_apply Elements.Book1.proposition_29''' F H G E FG EH EG
    euclid_finish
  have : ∠ I:F:G = ∠ I:H:E := by
    euclid_apply Elements.Book1.proposition_29''' G E F H FG EH FH
    euclid_finish
  euclid_assert (△ E:H:I).congruent (△ G:F:I)
  euclid_apply Triangle.congruent_if (△ E:H:I) (△ G:F:I)
  euclid_finish

end UniGeo.Congruent
