import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Triangle

theorem theorem_2 : ∀ (R S T U : Point) (RS ST TR RU : Line),
  formTriangle R S T RS ST TR ∧
  distinctPointsOnLine R U RU ∧
  ST.intersectsLine RU ∧ U.onLine ST ∧ between S U T ∧
  |(S─U)| = |(T─U)| ∧|(R─T)| = |(R─S)|→
  ∠ R:S:U = ∠ R:T:U :=
by
  euclid_intros

  have : △R:S:U≅△R:T:U := by euclid_finish
  have : ∠ R:S:U = ∠ R:T:U := by
    euclid_apply (△R:S:U).congruent_if △R:T:U
    euclid_finish
  euclid_finish

end UniGeo.Triangle
