import SystemE
import Book.Prop13
import Book.Prop15
import Book.Prop27

namespace Elements.Book1

theorem proposition_28 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧
  (∠ e:g:b = ∠ g:h:d ∨ ∠ b:g:h + ∠ g:h:d = ∟ + ∟) →
  ¬(AB.intersectsLine CD) :=
by
  euclid_intros
  split_ors
  . euclid_apply (proposition_15 a b e h g AB EF)
    euclid_apply (proposition_27 a d g h AB CD EF)
    euclid_finish
  . euclid_apply (proposition_13 h g a b EF AB)
    euclid_apply (proposition_27 a d g h AB CD EF)
    euclid_finish

end Elements.Book1
