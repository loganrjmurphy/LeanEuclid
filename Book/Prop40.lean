import SystemE
import Book.Prop31
import Book.Prop38


namespace Elements.Book1

theorem proposition_40 : ∀  (a b c d e : Point) (AB BC AC CD DE AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d c e CD BC DE ∧ a.sameSide d BC ∧ b ≠ e ∧ |(b─c)| = |(c─e)| ∧
  distinctPointsOnLine a d AD ∧ (Triangle.area △ a:b:c = Triangle.area △ d:c:e) →
  ¬(AD.intersectsLine BC) :=
by
  euclid_intros
  by_contra
  euclid_apply (proposition_31 a b c BC) as AF
  euclid_apply (intersection_lines AF CD) as f
  by_cases (a = f)
  . -- Omitted by Euclid.
    euclid_apply (intersection_lines AF DE) as g
    euclid_apply (line_from_points g c) as GC
    euclid_apply (proposition_38 a b c g c e AF BC AB AC GC DE)
    euclid_assert (Triangle.area △ d:c:e : ℝ) = (Triangle.area △ g:c:e)
    euclid_finish
  . euclid_apply (line_from_points f e) as FE
    euclid_apply (proposition_38 a b c f c e AF BC AB AC CD FE)
    euclid_assert ((Triangle.area △ d:c:e : ℝ) = Triangle.area △ f:c:e)
    euclid_finish

end Elements.Book1
