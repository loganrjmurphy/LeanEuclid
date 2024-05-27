import SystemE
import Book.Prop26
import Book.Prop29


namespace Elements.Book1

theorem proposition_34 : ∀ (a b c d : Point) (AB CD AC BD BC : Line),
  formParallelogram a b c d AB CD AC BD ∧ distinctPointsOnLine b c BC →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c  = ∠ c:d:b ∧
  Triangle.area △ a:b:c = Triangle.area △ d:c:b :=
by
  euclid_intros
  euclid_apply (proposition_29''' a d b c AB CD BC)
  euclid_apply (proposition_29''' a d c b AC BD BC)
  euclid_apply (proposition_26 a b c d c b AB BC AC CD BC BD)
  euclid_finish

theorem proposition_34' : ∀ (a b c d : Point) (AB CD AC BD : Line),
  formParallelogram a b c d AB CD AC BD →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b :=
by
  euclid_intros
  euclid_apply (line_from_points b c) as BC
  euclid_apply (proposition_34 a b c d AB CD AC BD BC)
  euclid_finish

end Elements.Book1
