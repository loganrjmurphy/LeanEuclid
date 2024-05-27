import SystemE
import Book.Prop01
import Book.Prop04
import Book.Prop09

namespace Elements.Book1

theorem proposition_10 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ d : Point, (between a d b) ∧ (|(a─d)| = |(d─b)|) :=
by
  euclid_intros
  euclid_apply (proposition_1 a b AB) as c
  euclid_apply (line_from_points c a) as AC
  euclid_apply (line_from_points c b ) as BC
  euclid_apply (proposition_9' c a b AC BC) as d'
  euclid_apply (line_from_points c d') as CD
  euclid_apply (intersection_lines CD AB) as d
  euclid_apply (proposition_4 c a d c b d AC AB CD BC AB CD)
  use d
  euclid_finish

end Elements.Book1
