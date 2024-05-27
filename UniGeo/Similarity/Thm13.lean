import SystemE
import Book.Prop15
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_13 : ∀ (P Q R S T : Point) (PR QS PS QR : Line),
  formTriangle P R T PR QR PS ∧
  formTriangle Q S T QS PS QR ∧
  between P T S ∧
  between Q T R ∧
  ¬ PR.intersectsLine QS →
  (△ P:R:T).similar (△ S:Q:T) :=
by
  euclid_intros
  have : ∠ Q:T:S = ∠ P:T:R := by
    euclid_apply Elements.Book1.proposition_15 P S R Q T PS QR
    euclid_finish
  have: ∠ R:P:T = ∠ Q:S:T := by
    euclid_apply Elements.Book1.proposition_29''' R Q P S PR QS PS
    euclid_finish
  euclid_finish

end UniGeo.Similarity
