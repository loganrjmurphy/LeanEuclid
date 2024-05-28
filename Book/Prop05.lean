import SystemE
import Book.Prop03
import Book.Prop04

namespace Elements.Book1

theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB b d (c─e)) as f
  euclid_apply (proposition_3 a e f a AC AB) as g
  euclid_apply (line_from_points c f) as FC
  euclid_apply (line_from_points b g) as GB
  euclid_apply (proposition_4 a f c a g b AB FC AC AC GB AB)
  euclid_apply (proposition_4 f b c g c b AB BC FC AC BC GB)
  euclid_apply (sum_angles_onlyif b a g c AB GB)
  euclid_apply (sum_angles_onlyif c a f b AC FC)
  euclid_finish

/--
A restriction of proposition_5.
-/
theorem proposition_5' : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) →
  (∠ a:b:c = ∠ a:c:b) :=
by
  euclid_intros
  euclid_apply (extend_point AB a b) as d
  euclid_apply (extend_point AC a c) as e
  euclid_apply (proposition_5 a b c d e AB BC AC)
  euclid_finish

end Elements.Book1
