import SystemE
import Book.Prop01
import Book.Prop03
import Book.Prop05
import Book.Prop07
import Book.Prop08

namespace Elements.Book1

theorem proposition_9 : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, f ≠ a ∧ (∠ b:a:f = ∠ c:a:f) :=
by
  euclid_intros
  euclid_apply point_between_points_shorter_than AB a b (a─c) as d
  euclid_apply (proposition_3 a c a d AC AB) as e
  euclid_apply (line_from_points d e) as DE
  euclid_apply (proposition_1' d e a DE) as f
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points a f) as AF
  use f
  have : ¬(f.onLine AB) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f d e AB DE FE)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  have : ¬(f.onLine AC) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f e d AC DE FD)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  euclid_apply (proposition_8 a d f a e f AB FD AF AC FE AF)
  euclid_finish

theorem proposition_9' : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, (f.sameSide c AB) ∧ (f.sameSide b AC) ∧ (∠ b:a:f = ∠ c:a:f) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB a b (a─c)) as d
  euclid_apply (proposition_3 a c a d AC AB) as e
  euclid_apply (line_from_points d e) as DE
  euclid_apply (proposition_1' d e a DE) as f
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points a f) as AF
  use f
  have : ¬(f.onLine AB) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f d e AB DE FE)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  have : ¬(f.onLine AC) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f e d AC DE FD)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  euclid_apply (proposition_8 a d f a e f AB FD AF AC FE AF)
  euclid_apply (intersection_lines AF DE) as g
  euclid_finish

end Elements.Book1
