import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_3 : ∀ (V W X Y Z : Point) (VW WZ VZ XY : Line),
  formTriangle V W Z VW WZ VZ ∧
  formTriangle X Y Z XY VZ WZ ∧
  between W X Z ∧
  between V Y Z ∧
  ¬ XY.intersectsLine VW →
  (△ X:Y:Z).similar (△ W:V:Z) :=
by
  euclid_intros
  have : ∠ X:Y:Z = ∠ W:V:Z := by
    euclid_apply Elements.Book1.proposition_29'''' X W Z Y V XY VW VZ
    euclid_finish
  euclid_finish

end UniGeo.Similarity
