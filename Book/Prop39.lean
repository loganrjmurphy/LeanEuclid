import SystemE
import Book.Prop31
import Book.Prop37


namespace Elements.Book1

theorem proposition_39 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ a.sameSide d BC ∧
  (△ a:b:c : ℝ) = (△ d:b:c) ∧ distinctPointsOnLine a d AD →
  ¬(AD.intersectsLine BC) :=
by
  euclid_intros
  by_contra
  by_cases c.sameSide d AB
  . euclid_apply (proposition_31 a b c BC) as AE
    euclid_apply (intersection_lines AE BD) as e
    euclid_apply (line_from_points e c) as EC
    euclid_apply (proposition_37 a b c e AB BC AC BD EC AE)
    euclid_assert (△ e:b:c : ℝ) = (△ d:b:c)
    euclid_finish
  . -- Omitted by Euclid.
    euclid_assert a.sameSide c BD
    euclid_apply (proposition_31 d b c BC) as DE
    euclid_apply (intersection_lines DE AB) as e
    euclid_apply (line_from_points e c) as EC
    euclid_apply (proposition_37 d b c e BD BC CD AB EC DE)
    euclid_assert (△ e:b:c : ℝ) = (△ a:b:c)

    -- Not sure why this is necessary.
    by_cases (between a e b)
    · euclid_apply (sum_areas_if a b e c AB)
      euclid_assert e = a
      euclid_finish
    · euclid_assert (between e a b)
      euclid_apply (sum_areas_if e b a c AB)
      euclid_assert e = a
      euclid_finish

end Elements.Book1
