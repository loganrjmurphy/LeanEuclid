import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_17 : ∀ (S V T U W : Point) (SV TU SU TV : Line),
  distinctPointsOnLine S V SV ∧
  distinctPointsOnLine T U TU ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine T V TV ∧
  twoLinesIntersectAtPoint SU TV W ∧ between S W U ∧ between T W V ∧
  ∠ T:U:W = ∠ U:T:W ∧
  ¬ SV.intersectsLine TU →
  ∠ W:V:S = ∠ W:S:V :=
by
  euclid_intros
  have : ∠ W:S:V = ∠ T:U:W := by
    euclid_apply Elements.Book1.proposition_29''' T V U S TU SV SU
    euclid_finish
  have : ∠ U:T:W = ∠ W:V:S := by
    euclid_apply Elements.Book1.proposition_29''' U S T V TU SV TV
    euclid_finish
  euclid_finish

end UniGeo.Parallel
