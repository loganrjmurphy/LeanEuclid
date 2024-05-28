import SystemE
import Book.Prop01
import Book.Prop03
import Book.Prop08

namespace Elements.Book1

theorem proposition_11 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB c a (c─b)) as d
  euclid_apply (proposition_3 c b c d AB AB) as e
  euclid_apply (proposition_1 d e AB) as f
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC)
  euclid_apply (perpendicular_if d e c f AB)
  use f
  euclid_finish

theorem proposition_11' : ∀ (a b c x : Point) (AB : Line),
  (distinctPointsOnLine a b AB) ∧ (between a c b) ∧ ¬(x.onLine AB) →
  exists f : Point, (f.sameSide x AB) ∧ (∠ a:c:f = ∟) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB c a (c─b)) as d
  euclid_apply (proposition_3 c b c d AB AB) as e
  euclid_apply (exists_point_opposite AB x) as h
  euclid_apply (proposition_1' d e h AB) as f
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC)
  euclid_apply (perpendicular_if d e c f AB)
  use f
  euclid_finish

theorem proposition_11'' : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  exists (f : Point), ¬(f.onLine AB) ∧ (∠ f:a:b = ∟) :=
by
  euclid_intros
  euclid_apply (extend_point AB b a) as c
  euclid_apply (proposition_11 c b a AB) as f
  use f
  euclid_finish

theorem proposition_11''' : ∀ (a b x : Point) (AB : Line),
  ¬(x.onLine AB) ∧ (distinctPointsOnLine a b AB) →
  exists (f : Point), ¬(f.onLine AB) ∧ (f.opposingSides x AB) ∧ (∠ f:a:b = ∟) :=
by
  euclid_intros
  euclid_apply (extend_point AB b a) as c
  euclid_apply (exists_point_opposite AB x) as g
  euclid_apply (proposition_11' c b a g AB) as f
  use f
  euclid_finish

end Elements.Book1
