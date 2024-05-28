import SystemE
import Book.Prop05
import Book.Prop18

namespace Elements.Book1

theorem proposition_19 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c > ∠ b:c:a) →
  (|(a─c)| > |(a─b)|) :=
by
  euclid_intros
  by_contra
  by_cases |(a─c)| = |(a─b)|
  . euclid_apply (proposition_5' a b c AB BC AC)
    euclid_finish
  . euclid_apply (proposition_18 a c b AC BC AB)
    euclid_finish

end Elements.Book1
