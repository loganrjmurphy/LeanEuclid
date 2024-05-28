import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_15 : ∀ (V W X Y Z : Point) (VY WX VW XY : Line),
  formTriangle V Y Z VY XY VW ∧
  formTriangle W X Z WX XY VW ∧
  between V Z W ∧
  between X Z Y ∧
  ∠ X:W:Z = ∠ V:Y:Z →
  (△ W:X:Z).similar (△ Y:V:Z) :=
by
  euclid_intros
  have : ∠ V:Z:Y = ∠ W:Z:X := by
    euclid_apply Elements.Book1.proposition_15 V W X Y Z VW XY
    euclid_finish
  euclid_finish

end UniGeo.Similarity
