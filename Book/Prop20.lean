import SystemE
import Book.Prop03
import Book.Prop05
import Book.Prop19

namespace Elements.Book1

theorem proposition_20 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC → |(b─a)| + |(a─c)| > |(b─c)| :=
by
  euclid_intros
  euclid_apply (extend_point_longer AB b a (c─a)) as d'
  euclid_apply (proposition_3 a d' a c AB AC) as d
  euclid_apply (line_from_points d c) as DC
  euclid_apply (proposition_5' a c d AC DC AB)
  euclid_apply (sum_angles_onlyif c b d a BC DC)
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1
