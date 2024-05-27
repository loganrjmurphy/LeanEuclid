import SystemE
import Book.Prop08
import Book.Prop10

namespace Elements.Book1

theorem proposition_12 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  exists h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) :=
by
  euclid_intros
  euclid_apply (exists_point_opposite AB c) as d
  euclid_apply (circle_from_points c d) as EFG
  euclid_apply (intersections_circle_line EFG AB) as (e, g)
  euclid_apply (proposition_10 e g AB) as h
  euclid_apply (line_from_points c g) as CG
  euclid_apply (line_from_points c h) as CH
  euclid_apply (line_from_points c e) as CE
  use h
  euclid_apply (proposition_8 h c g h c e CH CG AB CH CE AB)
  euclid_finish

end Elements.Book1
