import SystemE
import Book.Prop04
import Book.Prop13
import Book.Prop14
import Book.Prop16
import Book.Prop17
import Book.Prop30
import Book.Prop31
import Book.Prop41
import Book.Prop46

namespace Elements.Book1

-- WARNING: This proof is quite slow.
theorem proposition_47 : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| :=
by
  euclid_intros
  euclid_apply (proposition_46' b a c AB) as (f, g, FG, BF, AG)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)

  -- Missed by Euclid.
  have : (∠ a:b:c : ℝ) < ∟ := by
    euclid_apply (proposition_17 c a b AC AB BC)
    euclid_finish

  -- Missed by Euclid.
  have : ¬(d.onLine AB) := by
    by_contra
    euclid_apply (proposition_13 c b a d BC AB)
    euclid_finish

  -- Missed by Euclid.
  have : (d.sameSide c AB) := by
    euclid_apply (extend_point AB a b) as b'
    euclid_apply (proposition_16 c a b b' AC AB BC)
    euclid_assert (∠ c:b:b' : ℝ) > ∟
    euclid_finish

  -- Missed by Euclid.
  have : (∠ a:c:b : ℝ) < ∟ := by
    euclid_apply (proposition_17 b c a BC AC AB)
    euclid_finish

  -- Missed by Euclid.
  have : ¬(e.onLine AC) := by
    by_contra
    euclid_apply (proposition_13 b c a e BC AC)
    euclid_finish

  -- Missed by Euclid.
  have : (e.sameSide b AC) := by
    euclid_apply (extend_point AC a c) as c'
    euclid_apply (proposition_16 b a c c' AB AC BC)
    euclid_assert (∠ b:c:c' : ℝ) > ∟
    euclid_finish

  euclid_apply (proposition_31 a b d BD) as AL
  euclid_apply (proposition_30 AL CE BD)
  euclid_apply (intersection_lines AL DE) as l
  euclid_apply (intersection_lines AL BC) as l'
  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_14 b a c g AB AC AG)
  euclid_apply (proposition_14 c a b h AC AB AH)
  euclid_assert ((∠ d:b:a : ℝ) = ∠ f:b:c)
  euclid_assert ((∠ c:b:a : ℝ) + ∟ = ∠ c:b:f)
  euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
  euclid_assert ((Triangle.area △ a:b:d) = Triangle.area △ b:c:f)
  euclid_apply (proposition_41 l' b d l a AL BD BC DE AB AD)
  euclid_apply (proposition_41 g f b a c AG BF FG AB FC BC)
  euclid_assert ((Triangle.area △ g:f:b : ℝ) + (Triangle.area △ g:b:a) = (Triangle.area △ l':b:d) + (Triangle.area △ l':d:l))
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b k) as BK
  euclid_apply sum_angles_onlyif c e a b CE AC
  euclid_apply sum_angles_onlyif c k b a CK BC
  euclid_assert ((∠ e:c:a : ℝ) = (∠ k:c:b))
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_assert ((Triangle.area △ a:c:e : ℝ) = Triangle.area △ c:b:k)
  euclid_apply (proposition_41 l' c e l a AL CE BC DE AC AE)
  euclid_apply (proposition_41 h k c a b AH CK HK AC BK BC)
  euclid_assert ((Triangle.area △ k:c:a : ℝ) + (Triangle.area △ k:a:h) = (Triangle.area △ l':c:e) + (Triangle.area △ l':e:l))
  euclid_apply (rectangle_area b c d e BC DE BD CE)
  euclid_apply (rectangle_area b a f g AB FG BF AG)
  euclid_apply (rectangle_area a c h k AC HK AH CK)
  euclid_apply sum_parallelograms_area b c d e l' l BC DE BD CE
  euclid_apply parallelogram_area b l' d l BC DE BD AL
  euclid_assert ((Triangle.area △ b:d:e : ℝ) + (Triangle.area △ b:e:c) = (Triangle.area △ g:f:b) + (Triangle.area △ g:b:a) + (Triangle.area △ k:c:a) + (Triangle.area △ k:a:h))
  euclid_finish

end Elements.Book1
