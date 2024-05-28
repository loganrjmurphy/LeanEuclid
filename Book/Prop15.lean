import SystemE
import Book.Prop13

namespace Elements.Book1

theorem proposition_15 : ∀ (a b c d e : Point) (AB CD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧
  CD ≠ AB ∧ (between d e c) ∧ (between a e b) →
  (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d) :=
by
   euclid_intros
   euclid_apply (proposition_13 a e c d AB CD)
   euclid_apply (proposition_13 d e a b CD AB)
   euclid_apply (proposition_13 c e a b CD AB)
   euclid_finish

end Elements.Book1
