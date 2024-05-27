import SystemE

namespace Elements.Book1

theorem proposition_4 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ (∠ b:a:c = ∠ e:d:f) →
  |(b─c)| = |(e─f)| ∧ (∠ a:b:c = ∠ d:e:f) ∧ (∠ a:c:b = ∠ d:f:e) :=
by
  euclid_intros
  euclid_apply (superposition a b c d e f AB BC AC DE) as (b', c', BC', DC')
  euclid_assert b' = e
  euclid_assert ∠ e:d:c' = ∠ e:d:f
  euclid_assert DC' = DF
  euclid_assert c' = f
  euclid_finish

end Elements.Book1
