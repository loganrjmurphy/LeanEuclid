import SystemE
import Book.Prop01

namespace Elements.Book1

theorem proposition_2 : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ a ≠ b →
  ∃ l : Point, |(a─l)| = |(b─c)| :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (proposition_1 a b AB) as d
  euclid_apply (line_from_points d a ) as AE
  euclid_apply (line_from_points d b ) as BF
  euclid_apply (circle_from_points b c) as CGH
  euclid_apply (intersection_circle_line_extending_points CGH BF b d) as g
  euclid_apply (circle_from_points d g) as GKL
  euclid_apply (intersection_circle_line_extending_points GKL AE a d) as l
  euclid_apply (point_on_circle_onlyif b c g CGH)
  euclid_apply (point_on_circle_onlyif d l g GKL)
  euclid_apply (between_if l a d )
  euclid_apply (between_if g b d )
  use l
  euclid_finish

/-
An extension of proposition_2 to the case where a and b may be the same point.
-/
theorem proposition_2' :
  ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC →
    ∃ l : Point, |(a─l)| = |(b─c)| :=
by
  euclid_intros
  by_cases (a = b)
  . use c
    euclid_finish
  . euclid_apply proposition_2 a b c BC as l
    use l

end Elements.Book1
