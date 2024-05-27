import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Parallel

theorem theorem_4 : ∀ (S T U V W : Point) (SV TU SU TV : Line),
  distinctPointsOnLine S V SV ∧
  distinctPointsOnLine T U TU ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine T V TV ∧
  twoLinesIntersectAtPoint SU TV W ∧ between S W U ∧ between T W V ∧
  ∠ U:T:W = ∠ W:S:V ∧
  ¬ SV.intersectsLine TU →
  ∠ T:U:W = ∠ W:V:S :=
by
  euclid_intros
  have : ∠ W:S:V = ∠ T:U:W := by
    euclid_apply proposition_29''' T V U S TU SV SU
    euclid_finish
  have : ∠U:T:W = ∠W:V:S := by
    euclid_apply proposition_29''' U S T V TU SV TV
    euclid_finish
  have : ∠ W:S:V = ∠W:V:S := by euclid_finish
  euclid_finish

end UniGeo.Parallel
