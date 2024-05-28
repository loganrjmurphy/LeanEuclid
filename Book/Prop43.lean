import SystemE
import Book.Prop34


namespace Elements.Book1

theorem proposition_43 : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  (Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) :=
by
  euclid_intros
  euclid_apply (proposition_34 d a c b AD BC CD AB AC)
  euclid_apply (proposition_34 h a k e AD EF GH AB AC)
  euclid_apply (proposition_34 f k c g EF BC CD GH AC)
  euclid_assert (Triangle.area △ a:e:k : ℝ) + (Triangle.area △ k:g:c) = (Triangle.area △ a:h:k) + (Triangle.area △ k:f:c)
  euclid_assert (Triangle.area △ a:h:k : ℝ) + (Triangle.area △ k:f:c) + (Triangle.area △ h:k:f) + (Triangle.area △ h:f:d) = (Triangle.area △ d:a:c)
  euclid_finish

end Elements.Book1
