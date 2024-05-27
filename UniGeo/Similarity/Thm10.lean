import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_10 : ∀ (P Q R S T : Point) (PQ ST PT QS : Line),
  formTriangle P R T PQ ST PT ∧
  formTriangle Q S R QS ST PQ ∧
  between P R Q ∧
  between S R T ∧
  ∠ R:P:T = ∠ R:S:Q →
  (△ P:R:T).similar (△ S:R:Q) :=
by
  euclid_intros
  have : ∠ Q:R:S = ∠ P:R:T := by
    euclid_apply Elements.Book1.proposition_15 S T P Q R ST PQ
    euclid_finish
  euclid_finish

end UniGeo.Similarity
