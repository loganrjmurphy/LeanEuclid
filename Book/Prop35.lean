import SystemE
import Book.Prop04
import Book.Prop29
import Book.Prop34


namespace Elements.Book1

theorem proposition_35 : ∀ (a b c d e f g : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC ∧
  between a d e ∧ between d e f ∧ g.onLine CD ∧ g.onLine EB →
  Triangle.area △a:b:d + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f :=
by
  euclid_intros
  euclid_apply (proposition_34' a d b c AF BC AB CD)
  euclid_apply (proposition_34' e f b c AF BC EB FC)
  euclid_assert (|(a─d)| = |(e─f)|)
  euclid_assert (|(a─e)| = |(d─f)|)
  euclid_apply (proposition_29'''' c b f d a CD AB AF)
  euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD)
  euclid_finish

theorem proposition_35' : ∀ (a b c d e f : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC →
  Triangle.area △a:b:d  + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f :=
by
  euclid_intros
  euclid_apply (proposition_34' a d b c AF BC AB CD)
  euclid_apply (proposition_34' e f b c AF BC EB FC)
  euclid_assert (|(a─d)| = |(e─f)|)
  by_cases (between a d f)
  · euclid_apply (intersection_lines CD EB) as g
    by_cases (between a d e)
    · euclid_apply (proposition_35 a b c d e f g AF BC AB CD EB FC)
      euclid_finish
    · euclid_apply (proposition_29'''' c b f d a CD AB AF)
      euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD)
      euclid_finish
  · by_cases (a = e)
    · euclid_finish
    · euclid_apply (intersection_lines FC AB) as g
      by_cases (between e f a)
      · euclid_apply (proposition_35 e b c f a d g AF BC EB FC AB CD)
        euclid_finish
      · euclid_apply (proposition_29'''' c b d f e FC EB AF)
        euclid_apply (proposition_4 e a b f d c AF AB EB AF CD FC)
        by_cases (f = a)
        · euclid_finish
        · euclid_assert (Triangle.area △ e:a:b + Triangle.area △ g:b:c = Triangle.area △ f:d:c + Triangle.area △ g:b:c)
          euclid_finish

end Elements.Book1
