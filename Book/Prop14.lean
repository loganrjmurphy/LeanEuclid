import SystemE
import Book.Prop13

namespace Elements.Book1

theorem proposition_14 : ∀ (a b c d : Point) (AB BC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ (c.opposingSides d AB) ∧
  (∠ a:b:c + ∠ a:b:d) = ∟ + ∟ →
  BC = BD :=
by
  euclid_intros
  by_contra
  euclid_apply (extend_point BC c b) as e
  euclid_apply (proposition_13 a b e c AB BC)
  by_cases a.sameSide e BD
  . euclid_apply (sum_angles_onlyif b a d e AB BD)
    euclid_finish
  . -- Omitted by Euclid.
    euclid_apply (sum_angles_onlyif b a e d AB BC)
    euclid_finish

end Elements.Book1
