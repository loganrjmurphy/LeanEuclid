import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Quadrilateral

theorem theorem_4 : ∀ (S T U V R : Point) (ST TU RU RS RT SU : Line),
  formQuadrilateral S T R U ST RU RS TU ∧
  distinctPointsOnLine T R RT ∧
  distinctPointsOnLine S U SU ∧
  twoLinesIntersectAtPoint RT SU V ∧
  ¬ RU.intersectsLine ST ∧
  |(R─T)|=|(S─U)| ∧ ¬ TU.intersectsLine RS → ∠ R:S:T =∟
   :=
by
  euclid_intros
  have :|(R─S)| = |(T─U)| := by
    euclid_apply proposition_29''' S U T R ST RU RT
    euclid_apply proposition_29''' U S T R TU RS RT
    euclid_assert △ U:T:R ≅ △S:R:T
    euclid_apply (△ U:T:R).congruent_if △S:R:T
    euclid_finish
  have : △R:S:T≅△U:T:S := by euclid_finish
  have : ∠R:S:T = ∠S:T:U := by
    euclid_apply (△R:S:T).congruent_if △U:T:S
    euclid_finish
  have : ∠R:S:T  + ∠S:T:U = ∟ +∟ := by
    euclid_apply proposition_29''''' R U S T RS TU ST
    euclid_finish
  have : ∠R:S:T  + ∠R:S:T = ∟ +∟ := by euclid_finish
  have : ∠R:S:T = ∟ := by euclid_finish
  euclid_finish

end UniGeo.Quadrilateral
