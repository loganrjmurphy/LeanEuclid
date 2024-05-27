import SystemE
import Book.Prop02

namespace Elements.Book1

theorem proposition_3 : ∀ (a b c₀ c₁ : Point) (AB C : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c₀ c₁ C ∧ |(a─b)| > |(c₀─c₁)| →
  ∃ e : Point, between a e b ∧ |(a─e)| = |(c₀─c₁)| :=
by
  euclid_intros
  euclid_apply (proposition_2' a c₀ c₁ C) as d
  euclid_apply (circle_from_points a d) as DEF
  euclid_apply (intersection_circle_line_between_points DEF AB a b) as e
  euclid_apply (point_on_circle_onlyif a d e)
  use e
  euclid_finish

end Elements.Book1
