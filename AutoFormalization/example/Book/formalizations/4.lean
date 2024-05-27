import SystemE
import Book.Prop13
import Book.Prop29
import Book.Prop31


namespace Elements.Book1

theorem proposition_32 : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  ∠ a:c:d = ∠ c:a:b + ∠ a:b:c ∧
  ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ :=
by
  euclid_intros

  have : (∠ a:c:d : ℝ) = (∠ c:a:b) + (∠ a:b:c) := by
    euclid_apply (proposition_31 c a b AB ) as CE
    euclid_apply (point_on_line_same_side BC CE a ) as e
    euclid_apply (proposition_29''' b e a c AB CE AC)
    euclid_apply (proposition_29'''' e a d c b CE AB BC)
    euclid_finish

  constructor
  · assumption
  · euclid_apply (proposition_13 a c b d AC BC)
    euclid_finish

end Elements.Book1
