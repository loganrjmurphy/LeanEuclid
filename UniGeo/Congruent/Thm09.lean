import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_9 : ∀ (U V W X Y : Point) (UW VX VW UX : Line),
  formTriangle U X Y UX VX UW ∧
  formTriangle V W Y VW UW VX ∧
  between U Y W ∧
  between V Y X ∧
  ∠ V:W:Y = ∠ X:U:Y ∧
  |(W─Y)| = |(U─Y)| →
  (△ V:W:Y).congruent (△ X:U:Y) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 U W X V Y UW VX
  euclid_finish

end UniGeo.Congruent
