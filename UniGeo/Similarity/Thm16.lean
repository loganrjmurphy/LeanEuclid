import SystemE
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_16 : ∀ (Q R S T U : Point) (QS SU QU RT : Line),
  formTriangle Q S U QS SU QU ∧
  formTriangle R T U RT QU SU ∧
  between Q T U ∧
  between S R U ∧
  |(R─U)| / |(S─U)| = |(T─U)| / |(Q─U)| →
  (△ R:T:U).similar (△ S:Q:U) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Similarity
