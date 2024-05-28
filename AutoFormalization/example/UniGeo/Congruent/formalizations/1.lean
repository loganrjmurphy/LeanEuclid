import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Congruent

theorem theorem_1 : ∀ (U V W X Y : Point) (UW VX UX WY VY : Line),
  formTriangle U V X UW VX UX ∧
  formTriangle V W Y UW WY VY ∧
  between U V W ∧
  X.sameSide Y UW ∧
  ∠ V:Y:W = ∠ U:X:V ∧
  |(W─Y)| = |(V─X)| ∧ |(V─Y)| = |(U─X)| ∧ |(U─V)| = |(V─W)| →
  (△ V:W:Y).congruent (△ U:V:X) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Congruent
