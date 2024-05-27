import SystemE
import Book.Prop07

namespace Elements.Book1

theorem proposition_8 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| →
  ∠ b:a:c = ∠ e:d:f :=
by
    euclid_intros
    euclid_apply (superposition b c a e f d BC AC AB EF) as (c', g, CG', EG)
    euclid_assert c' = f
    by_cases d = g
    · euclid_finish
    · euclid_apply (proposition_7 e f d g EF DE DF EG CG')
      euclid_finish

end Elements.Book1
