import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Similarity

theorem theorem_4 : ∀ (U V W X Y : Point) (UX VW VX UW : Line),
  formTriangle X Y V UX VW VX ∧
  formTriangle W Y U VW UX UW ∧
  between X Y U ∧
  between W Y V ∧
  ∠ Y:X:V = ∠ W:U:Y →
  (△ U:W:Y).similar (△ X:V:Y) :=
by
  euclid_intros
  have : ∠V:Y:X = ∠U:Y:W := by
    euclid_apply proposition_15 X U V W Y UX VW
    euclid_finish
  euclid_finish

end UniGeo.Similarity
