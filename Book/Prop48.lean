import SystemE
import Book.Prop03
import Book.Prop08
import Book.Prop11
import Book.Prop47

namespace Elements.Book1

theorem proposition_48 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| →
  ∠ b:a:c = ∟ :=
by
  euclid_intros
  euclid_apply (proposition_11'' a c AC) as d'
  euclid_apply (line_from_points a d') as AD
  euclid_apply (extend_point AD d' a) as d''
  euclid_apply (extend_point_longer AD d'' a (a─b)) as d'''
  euclid_apply (proposition_3 a d''' a b AD AB) as d
  euclid_apply (line_from_points d c) as DC
  euclid_assert (|(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|)
  euclid_assert (|(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)|)
  euclid_apply (proposition_47 a d c AD DC AC)
  euclid_assert (|(d─c)| = |(b─c)|)
  euclid_apply (proposition_8 a b c a d c AB BC AC AD DC AC)
  euclid_finish

end Elements.Book1
