import SystemE
import Book.Prop34
import Book.Prop37


namespace Elements.Book1

theorem proposition_41 : ∀ (a b c d e : Point) (AE BC AB CD BE CE : Line),
  formParallelogram a d b c AE BC AB CD ∧ formTriangle e b c BE BC CE ∧ e.onLine AE ∧ ¬(AE.intersectsLine  BC) →
  (Triangle.area △ a:b:c : ℝ) + (Triangle.area △ a:c:d) = (Triangle.area △ e:b:c) + (Triangle.area △ e :b :c) :=
by
  euclid_intros
  euclid_apply (line_from_points a c) as AC
  by_cases (a = e)
  . -- Omitted by Euclid.
    euclid_assert (Triangle.area △ a:b:c : ℝ) = (Triangle.area △ e:b:c)
    euclid_apply (proposition_34 d a c b AE BC CD AB AC)
    euclid_finish
  . euclid_apply (proposition_37' a b c e AB BC AC BE CE AE)
    euclid_apply (proposition_34 d a c b AE BC CD AB AC)
    euclid_finish

end Elements.Book1
