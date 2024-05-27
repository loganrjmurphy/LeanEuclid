import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_14 : ∀ (V W X Y Z : Point) (VZ XY VY XZ : Line),
  formTriangle V W Z VY XZ VZ ∧
  formTriangle W X Y XZ XY VY ∧
  between V W Y ∧
  between X W Z ∧
  |(W─Z)| / |(W─X)| = |(V─W)| / |(W─Y)| →
  (△ V:W:Z).similar (△ Y:W:X) :=
by
  euclid_intros
  have : ∠ X:W:Y = ∠ V:W:Z := by
    euclid_apply Elements.Book1.proposition_15 X Z V Y W XZ VY
    euclid_finish
  euclid_finish

end UniGeo.Similarity
