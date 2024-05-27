import SystemE
import Book.Prop04
import Book.Prop24

namespace Elements.Book1

theorem proposition_25 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (|(b─c)| > |(e─f)|) →
  (∠ b:a:c > ∠ e:d:f) :=
by
  euclid_intros
  by_contra
  by_cases (∠ b:a:c = ∠ e:d:f)
  · euclid_apply (proposition_4 a b c d e f AB BC AC DE EF DF)
    euclid_finish
  · euclid_assert (∠ b:a:c < ∠ e:d:f)
    euclid_apply (proposition_24 d e f a b c DE EF DF AB BC AC)
    euclid_finish

end Elements.Book1
