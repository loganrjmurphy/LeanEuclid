import SystemE
import Book.Prop03
import Book.Prop05
import Book.Prop16

namespace Elements.Book1

theorem proposition_18 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─c)| > |(a─b)|) →
  (∠ a:b:c > ∠ b:c:a) :=
by
  euclid_intros
  euclid_apply (proposition_3 a c a b AC AB) as d
  euclid_apply (line_from_points b d) as BD
  euclid_apply (proposition_16 b c d a BC AC BD)
  euclid_apply (proposition_5' a b d AB BD AC)
  euclid_apply (sum_angles_if b a c d AB BC)
  euclid_finish

end Elements.Book1
