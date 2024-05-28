import SystemE
import Book.Prop13
import Book.Prop16

namespace Elements.Book1

theorem proposition_17 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  ∠ a:b:c + ∠ b:c:a < ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (extend_point BC b c) as d
  euclid_apply (proposition_16 a b c d AB BC AC)
  euclid_apply (proposition_13 a c b d AC BC)
  euclid_finish

end Elements.Book1
