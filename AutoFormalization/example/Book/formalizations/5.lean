import SystemE
import Book.Prop10
import Book.Prop23
import Book.Prop31
import Book.Prop38
import Book.Prop41


namespace Elements.Book1

theorem proposition_42 : ∀ (a b c d₁ d₂ d₃ : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g e c' : Point) (FG EC EF CG : Line), formParallelogram f g e c' FG EC EF CG ∧
  (∠ c':e:f = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c' + Triangle.area △ f:c':g = Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_10 b c BC) as e
  euclid_apply (line_from_points a e) as AE
  euclid_apply (proposition_23''' e c d₂ d₁ d₃ a BC D₁₂ D₂₃) as f'
  euclid_apply (line_from_points e f') as EF
  euclid_apply (proposition_31 a b c BC) as AG
  euclid_apply (intersection_lines AG EF) as f
  euclid_apply (proposition_31 c e f EF) as CG
  euclid_apply (intersection_lines CG AG) as g
  euclid_assert (formParallelogram f g e c AG BC EF CG)
  euclid_apply (proposition_38 a b e a e c AG BC AB AE AE AC)
  euclid_apply (proposition_41 f e c g a AG BC EF CG AE AC)
  use f, g, e, c, AG, BC, EF, CG
  euclid_finish

theorem proposition_42' : ∀ (a b c d₁ d₂ d₃ e : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ between b e c ∧ (|(b─e)| = |(e─c)|) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g : Point) (FG EF CG : Line), a.sameSide f BC ∧ formParallelogram f g e c FG BC EF CG ∧
  (∠ c:e:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c : ℝ) + (Triangle.area △ f:c:g) = (Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (line_from_points a e) as AE
  euclid_apply (proposition_23''' e c d₂ d₁ d₃ a BC D₁₂ D₂₃) as fn
  euclid_apply (line_from_points e fn) as EF
  euclid_apply (proposition_31 a b c BC) as AG
  euclid_apply (intersection_lines AG EF) as f
  euclid_apply (proposition_31 c e f EF) as CG
  euclid_apply (intersection_lines CG AG) as g
  euclid_assert (formParallelogram f g e c AG BC EF CG)
  euclid_apply (proposition_38 a b e a e c AG BC AB AE AE AC)
  euclid_apply (proposition_41 f e c g a AG BC EF CG AE AC)
  use f, g, AG, EF, CG
  euclid_finish

theorem proposition_42'' : ∀ (a b c d₁ d₂ d₃ h i : Point) (AB BC AC D₁₂ D₂₃ HI : Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ ∧ distinctPointsOnLine h i HI →
  ∃ (f g j : Point) (FG FI GJ : Line), between h i j ∧ formParallelogram f g i j FG HI FI GJ ∧
  (∠ j:i:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:i:j : ℝ) + (Triangle.area △ f:j:g) = (Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_10 b c BC) as e
  euclid_apply (extend_point_longer HI h i (e─c)) as i''
  euclid_apply (proposition_3' i i'' e c HI BC) as j
  euclid_apply (extend_point_longer HI i h (e─c)) as h'
  euclid_apply (proposition_3' i h' e c HI BC) as k
  euclid_apply (proposition_23 k j b a c HI AB BC) as l'
  euclid_apply (line_from_points k l') as KL
  euclid_apply (extend_point_longer KL k l' (a─b)) as l''
  euclid_apply (proposition_3' k l'' b a KL AB) as l
  euclid_apply (line_from_points l j) as LJ
  euclid_apply (proposition_4 k j l b c a HI LJ KL BC AC AB)
  euclid_apply (proposition_42' l k j d₁ d₂ d₃ i KL HI LJ D₁₂ D₂₃) as (f, g, FG, FI, GJ)
  use f, g, j, FG, FI, GJ
  euclid_finish

theorem proposition_42''' : ∀ (a b c d₁ d₂ d₃ h i x : Point) (AB BC AC D₁₂ D₂₃ HI : Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ ¬(x.onLine HI) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ ∧ distinctPointsOnLine h i HI →
  ∃ (f g j : Point) (FG FI GJ : Line), f.sameSide x HI ∧ between h i j ∧ formParallelogram f g i j FG HI FI GJ ∧
  (∠ j:i:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:i:j : ℝ) + (Triangle.area △ f:j:g) = (Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_10 b c BC) as e
  euclid_apply (extend_point_longer HI h i (e─c)) as i''
  euclid_apply (proposition_3' i i'' e c HI BC) as j
  euclid_apply (extend_point_longer HI i h (e─c)) as h'
  euclid_apply (proposition_3' i h' e c HI BC) as k
  euclid_apply (proposition_23''' k j b a c x HI AB BC) as l'
  euclid_apply (line_from_points k l') as KL
  euclid_apply (extend_point_longer KL k l' (a─b)) as l''
  euclid_apply (proposition_3' k l'' b a KL AB) as l
  euclid_apply (line_from_points l j) as LJ
  euclid_apply (proposition_4 k j l b c a HI LJ KL BC AC AB)
  euclid_apply (proposition_42' l k j d₁ d₂ d₃ i KL HI LJ D₁₂ D₂₃) as (f, g, FG, FI, GJ)
  use f, g, j, FG, FI, GJ
  euclid_finish

end Elements.Book1
