import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Similarity

theorem theorem_5 : ∀ (U T R S : Point) (TU SU RU RS : Line),
  formTriangle U T S TU RS SU ∧
  formTriangle U R S RU RS SU ∧
  between R T S ∧
  ∠ R:U:S = ∟ ∧
  ∠ U:T:S = ∟ ∧ ∠ U:T:R = ∟ →
  (△ S:T:U).similar (△ U:T:R) :=
by
  euclid_intros
  have : ∠ U:T:R = ∟ := by
    euclid_apply proposition_13 U T R S TU RS
    euclid_finish
  have : ∠U:R:T+∠R:U:T=∟ := by
    euclid_apply proposition_32 U R T S RU RS TU
    euclid_finish
  have : ∠U:R:T+∠U:S:T=∟  := by
    euclid_apply extend_point RS R S as d
    euclid_apply proposition_32 U R S d RU RS SU
    euclid_finish
  euclid_assert ∠U:R:T+∠U:S:T = ∠U:R:T+∠R:U:T
  euclid_finish

end UniGeo.Similarity
