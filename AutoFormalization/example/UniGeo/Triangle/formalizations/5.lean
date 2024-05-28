import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Triangle

theorem theorem_5 : ∀ (T S W R V U : Point) (ST SW TW RV RU UV : Line),
  formTriangle S T W ST TW SW ∧
  formTriangle R U V RU UV RV ∧
  ∠ T:S:W = ∠ V:R:U ∧
  |(S─W)| / |(R─V)| = |(S─T)| / |(R─U)| →
  ∠ S:W:T = ∠ R:V:U :=
by
  euclid_intros
  have : △S:T:W~△R:U:V:= by euclid_finish
  have: ∠ S:W:T = ∠ R:V:U := by
    euclid_apply (△S:T:W).similar_if △R:U:V
    euclid_finish
  euclid_finish

end UniGeo.Triangle
