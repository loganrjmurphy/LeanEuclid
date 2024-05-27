import SystemE
import Book.Prop03
import Book.Prop04

namespace Elements.Book1

theorem proposition_6 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| :=
by
  euclid_intros
  by_contra
  by_cases |(a─b)| > |(a─c)|
  . euclid_apply (proposition_3 b a a c AB AC) as d
    euclid_apply (line_from_points d c) as DC
    euclid_apply proposition_4 b d c c a b AB DC BC AC AB BC
    euclid_finish
  . euclid_apply (proposition_3 c a a b AC AB) as d
    euclid_apply (line_from_points d b) as DB
    euclid_apply (proposition_4 c d b b a c AC DB BC AB AC BC)
    euclid_finish

end Elements.Book1
