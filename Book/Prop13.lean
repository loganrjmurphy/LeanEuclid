import SystemE
import Book.Prop11

namespace Elements.Book1

theorem proposition_13 : ∀ (a b c d : Point) (AB CD : Line),
  AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c →
  ∠ c:b:a + ∠ a:b:d = ∟ + ∟ :=
by
  euclid_intros
  by_cases ∠ c:b:a = ∠ a:b:d
  . euclid_finish
  . euclid_apply (proposition_11' d c b a CD) as e
    euclid_apply (line_from_points b e) as BE
    euclid_finish

end Elements.Book1
