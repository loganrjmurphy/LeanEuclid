import SystemE
import Book.Prop14
import Book.Prop29
import Book.Prop30
import Book.Prop33
import Book.Prop34
import Book.Prop42
import Book.Prop44


namespace Elements.Book1

theorem proposition_45 : ∀ (a b c d e₁ e₂ e₃ : Point) (AB BC CD AD DB E₁₂ E₂₃ : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB ∧
  formRectilinearAngle e₁ e₂ e₃ E₁₂ E₂₃ ∧ ∠ e₁:e₂:e₃ > 0 ∧ ∠ e₁:e₂:e₃ < ∟ + ∟ →
  ∃ (f l k m : Point) (FL KM FK LM : Line), formParallelogram f l k m FL KM FK LM ∧
  (∠ f:k:m = ∠ e₁:e₂:e₃) ∧ (Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_42 a b d e₁ e₂ e₃ AB DB AD E₁₂ E₂₃) as (f, g, k, h , FG, KH, FK, GH)
  euclid_apply (proposition_44' g h d b c e₁ e₂ e₃ k GH DB BC CD E₁₂ E₂₃) as (m, l, HM, G, LM)
  euclid_assert ((∠ h:k:f : ℝ) = ∠ g:h:m)
  euclid_assert ((∠ h:k:f : ℝ) + (∠ k:h:g) = (∠ g:h:m) + (∠ k:h:g))
  euclid_apply (proposition_29''''' f g k h FK GH KH)
  euclid_assert ((∠ k:h:g : ℝ) + (∠ g:h:m) = ∟ + ∟)
  euclid_apply (proposition_14 g h k m GH KH HM)
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_assert ((∠ m:h:g : ℝ) + (∠ h:g:l) = (∠ h:g:f) + (∠ h:g:l))
  euclid_apply (proposition_29''''' l m g h G HM GH)
  euclid_assert ((∠ h:g:f : ℝ) + (∠ h:g:l) = ∟ + ∟)
  euclid_apply (proposition_14 h g f l GH FG G)
  euclid_apply (proposition_34' f g k h FG KH FK GH)
  euclid_apply (proposition_34' h m g l HM G GH LM)
  euclid_assert (|(k─f)| = |(m─l)|)
  euclid_apply (proposition_30 FK LM GH)
  euclid_assert (|(f─l)| = |(k─m)|)
  euclid_apply (proposition_33 f l k m FG KH FK LM)
  use f, l, k, m, FG, KH, FK, LM
  euclid_finish

end Elements.Book1
