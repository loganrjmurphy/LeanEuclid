import SystemE
import Book.Prop16

namespace Elements.Book1

theorem proposition_27 : ∀ (a d e f : Point) (AE FD EF : Line),
  distinctPointsOnLine a e AE ∧ distinctPointsOnLine f d FD ∧ distinctPointsOnLine e f EF ∧
  a.opposingSides d EF ∧ (∠ a:e:f = ∠ e:f:d) →
  ¬(AE.intersectsLine FD) :=
by
  euclid_intros
  by_contra
  euclid_apply (extend_point AE a e) as b
  euclid_apply (intersection_lines AE FD) as g
  by_cases (g.sameSide b EF)
  . euclid_apply (proposition_16 f g e a FD AE EF)
    euclid_finish
  . -- Omitted by Euclid.
    euclid_apply (proposition_16 e g f d AE FD EF)
    euclid_finish

end Elements.Book1
