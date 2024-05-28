import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_20 : ∀ (P R T S U Q : Point) (PR RT TP SU UQ QS : Line),
  formTriangle P R T PR RT TP ∧
  formTriangle S U Q SU UQ QS ∧
  ∠ P:R:T = ∠ S:U:Q ∧
  ∠ P:T:R = ∠ S:Q:U →
  |(R─T)| / |(Q─U)| = |(P─T)| / |(Q─S)| :=
by
  euclid_intros
  euclid_assert (△ P:R:T).similar (△ S:U:Q)
  euclid_apply Triangle.similar_if (△ P:R:T) (△ S:U:Q)
  euclid_finish

end UniGeo.Triangle
