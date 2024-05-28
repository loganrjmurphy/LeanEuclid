import SystemE
import Book.Prop03
import Book.Prop04
import Book.Prop10
import Book.Prop15

namespace Elements.Book1

theorem proposition_16 : ∀ (a b c d : Point) (AB BC AC: Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  (∠ a:c:d > ∠ c:b:a) ∧ (∠ a:c:d > ∠ b:a:c) :=
by
  euclid_intros
  constructor
  · -- Omitted by Euclid.
    euclid_apply (proposition_10 b c BC) as e
    euclid_apply (line_from_points a e) as AE
    euclid_apply (extend_point_longer AE a e (a─e)) as f'
    euclid_apply (proposition_3 e f' a e AE AE) as f
    euclid_apply (line_from_points f c) as FC
    euclid_apply (proposition_15 b c a f e BC AE)
    euclid_apply (proposition_4 e b a e c f BC AB AE BC FC AE)
    euclid_apply (extend_point AC a c) as g
    euclid_apply (proposition_15 a g b d c AC BC)
    euclid_finish
  · euclid_apply (proposition_10 a c AC) as e
    euclid_apply (line_from_points b e) as BE
    euclid_apply (extend_point_longer BE b e (b─e)) as f'
    euclid_apply (proposition_3 e f' b e BE BE) as f
    euclid_apply (line_from_points f c) as FC
    euclid_apply (proposition_15 a c b f e AC BE)
    euclid_apply (proposition_4 e b a e f c BE AB AC BE FC AC)
    euclid_finish

end Elements.Book1
