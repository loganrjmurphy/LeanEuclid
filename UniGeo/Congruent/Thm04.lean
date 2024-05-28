import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_4 : ∀ (U V W X Y : Point) (UW VX UX WY VY : Line),
  formTriangle U V X UW VX UX ∧
  formTriangle V W Y UW WY VY ∧
  between U V W ∧
  X.sameSide Y UW ∧
  ∠ V:Y:W = ∠ U:X:V ∧
  |(U─X)| = |(V─Y)| ∧
  ¬ UX.intersectsLine VY →
  (△ V:W:Y).congruent (△ U:V:X) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29'''' Y X W V U VY UX UW
  euclid_finish

end UniGeo.Congruent
