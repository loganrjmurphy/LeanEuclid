import SystemE
import Book.Prop03

namespace Elements.Book1

theorem proposition_22 : ∀ (a a' b b' c c' : Point) (A B C : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k f g : Point), (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply arbitrary_point as d
  euclid_apply (distinct_points d) as e'
  euclid_apply (line_from_points d e') as DE
  euclid_apply (extend_point_longer DE d e' (a─a')) as e''
  euclid_apply (extend_point_longer DE d e'' (b─b')) as e'''
  euclid_apply (extend_point_longer DE d e''' (c─c')) as e
  euclid_apply (proposition_3 d e a a' DE A ) as f
  euclid_apply (proposition_3 f e b b' DE B) as g
  euclid_apply (proposition_3 g e c c' DE C) as h
  euclid_apply (circle_from_points f d) as DKL
  euclid_apply (circle_from_points g h) as KLH
  -- Euclid didn't need to explicitly note the existence of i.
  euclid_apply (intersection_circle_line_extending_points KLH DE g h) as i
  euclid_apply (intersection_circles KLH DKL) as k
  use k, f, g
  euclid_apply (point_on_circle_onlyif f d k DKL)
  euclid_apply (point_on_circle_onlyif g k h KLH)
  euclid_finish

-- An extension of proposition 22 given a line and two points on it.
theorem proposition_22' : ∀ (a a' b b' c c' f e : Point) (A B C FE : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ distinctPointsOnLine f e FE ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k g : Point), g.onLine FE ∧ ¬(between g f e) ∧
  (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply (extend_point_longer FE f e (b─b')) as e'
  euclid_apply (extend_point_longer FE f e' (c─c')) as e''
  euclid_apply (proposition_3 f e'' a a' FE A) as d
  euclid_apply (proposition_3 f e'' b b' FE B) as g
  euclid_apply (proposition_3 g e'' c c' FE C) as h
  euclid_apply (circle_from_points f d) as DKL
  euclid_apply (circle_from_points g h) as KLH
  -- Euclid didn't need to explicitly note the existence of i.
  euclid_apply (intersection_circle_line_extending_points KLH FE g h) as i
  euclid_apply (intersection_circles KLH DKL) as k
  use k, g
  euclid_apply (point_on_circle_onlyif f d k DKL)
  euclid_apply (point_on_circle_onlyif g k h KLH)
  euclid_finish

theorem proposition_22'' : ∀ (a a' b b' c c' f e x : Point) (A B C FE : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ distinctPointsOnLine f e FE ∧ ¬(x.onLine FE) ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k g : Point), g.onLine FE ∧ ¬(between g f e) ∧ (k.sameSide x FE) ∧
  (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply (extend_point_longer FE f e (b─b')) as e'
  euclid_apply (extend_point_longer FE f e' (c─c')) as e''
  euclid_apply (proposition_3 f e'' a a' FE A) as d
  euclid_apply (proposition_3 f e'' b b' FE B) as g
  euclid_apply (proposition_3 g e'' c c' FE C) as h
  euclid_apply (circle_from_points f d) as DKL
  euclid_apply (circle_from_points g h) as KLH
  -- Euclid didn't need to explicitly note the existence of i.
  euclid_apply (intersection_circle_line_extending_points KLH FE g h) as i
  euclid_apply (intersection_same_side KLH DKL x g f FE) as k
  use k, g
  euclid_apply (point_on_circle_onlyif f d k DKL)
  euclid_apply (point_on_circle_onlyif g k h KLH)
  euclid_finish

end Elements.Book1
