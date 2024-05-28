import SystemE
import Book.Prop15
import Book.Prop29
import Book.Prop30
import Book.Prop31
import Book.Prop42
import Book.Prop43


namespace Elements.Book1

theorem proposition_44 : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃) :=
by
  euclid_intros
  euclid_apply (proposition_42'' c₁ c₂ c₃ d₁ d₂ d₃ a b C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ AB) as (g, f, e, FG, BG, EF)
  euclid_apply (proposition_31 a b g BG) as AH
  euclid_apply (proposition_30 AH EF BG)
  euclid_apply (intersection_lines AH FG) as h
  euclid_apply (line_from_points h b) as HB
  euclid_apply (proposition_29''''' e a f h EF AH FG)
  euclid_apply (intersection_lines HB EF) as k
  euclid_apply (proposition_31 k e a AB) as KL
  euclid_apply (proposition_30 KL FG AB)
  euclid_apply (intersection_lines AH KL) as l
  euclid_apply (intersection_lines BG KL) as m
  euclid_apply (proposition_43 h f k l g m e a b AH EF FG KL HB BG AB)
  euclid_apply (proposition_15 e a m g b AB BG)
  use m, l, BG, AH, KL
  euclid_finish

theorem proposition_44' : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ x : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), Point.opposingSides m x AB ∧ formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m) + (Triangle.area △ a:l:m) = (Triangle.area △ c₁:c₂:c₃) :=
by
  euclid_intros
  euclid_apply (proposition_42''' c₁ c₂ c₃ d₁ d₂ d₃ a b x C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ AB) as (g, f ,e ,FG, BG, EF)
  euclid_apply (proposition_31 a b g BG) as AH
  euclid_apply (proposition_30 AH EF BG)
  euclid_apply (intersection_lines AH FG) as h
  euclid_apply (line_from_points h b) as HB
  euclid_apply (proposition_29''''' e a f h EF AH FG)
  euclid_apply (intersection_lines HB EF) as k
  euclid_apply (proposition_31 k e a AB) as KL
  euclid_apply (proposition_30 KL FG AB)
  euclid_apply (intersection_lines AH KL) as l
  euclid_apply (intersection_lines BG KL) as m
  euclid_apply (proposition_43 h f k l g m e a b AH EF FG KL HB BG AB)
  euclid_apply (proposition_15 e a m g b AB BG)
  use m, l, BG, AH, KL
  euclid_finish

end Elements.Book1
