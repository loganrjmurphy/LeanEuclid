import SystemE
import Book.Prop16
import Book.Prop20

namespace Elements.Book1

theorem proposition_21 : ∀ (a b c d : Point) (AB BC AC BD DC : Line),
  formTriangle a b c AB BC AC ∧ (a.sameSide d BC) ∧ (c.sameSide d AB) ∧ (b.sameSide d AC) ∧
  distinctPointsOnLine b d BD ∧ distinctPointsOnLine d c DC →
  (|(b─d)| + |(d─c)| < |(b─a)| + |(a─c)|) ∧ (∠ b:d:c > ∠ b:a:c) :=
by
  euclid_intros
  euclid_apply (intersection_lines BD AC) as e
  euclid_apply (proposition_20 a b e AB BD AC)
  euclid_apply (proposition_20 e d c BD DC AC)
  constructor
  . euclid_finish
  . euclid_apply (proposition_16 c e d b AC BD DC)
    euclid_apply (proposition_16 b a e c AB AC BD)
    euclid_finish

end Elements.Book1
