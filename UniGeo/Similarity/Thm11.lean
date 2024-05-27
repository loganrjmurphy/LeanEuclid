import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_11 : ∀ (U V W X Y : Point) (VX WY VY WX : Line),
  formTriangle U V X VY VX WX ∧
  formTriangle U W Y WX WY VY ∧
  between V U Y ∧
  between W U X ∧
  |(U─V)| / |(U─W)| = |(U─X)| / |(U─Y)| →
  (△ U:V:X).similar (△ U:W:Y) :=
by
  euclid_intros
  have : ∠ W:U:Y = ∠ V:U:X := by
    euclid_apply Elements.Book1.proposition_15 X W V Y U WX VY
    euclid_finish
  euclid_finish

end UniGeo.Similarity
