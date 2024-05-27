import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_1 : ∀ (R S T U : Point) (RS ST RT TU RU : Line),
  formTriangle R S T RS ST RT ∧
  formTriangle R T U RT TU RU ∧
  S.opposingSides U RT ∧
  |(T─U)| = |(R─S)| ∧
  ¬ RS.intersectsLine TU →
  (△ R:T:U).congruent (△ T:R:S) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' S U R T RS TU RT
  euclid_finish

end UniGeo.Congruent
