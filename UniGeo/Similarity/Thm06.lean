import SystemE
import Book.Prop15
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_6 : ∀ (U V W X Y : Point) (VY WX VW XY : Line),
  formTriangle U V Y VW VY XY ∧
  formTriangle U W X VW WX XY ∧
  between V U W ∧
  between X U Y ∧
  ¬ WX.intersectsLine VY →
  (△ U:W:X).similar (△ U:V:Y) :=
by
  euclid_intros
  have : ∠ V:U:Y = ∠ W:U:X := by
    euclid_apply Elements.Book1.proposition_15 V W X Y U VW XY
    euclid_finish
  have : ∠ U:X:W = ∠ U:Y:V := by
    euclid_apply Elements.Book1.proposition_29''' W V X Y WX VY XY
    euclid_finish
  euclid_finish

end UniGeo.Similarity
