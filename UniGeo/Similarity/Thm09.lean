import SystemE
import Book.Prop15
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_9 : ∀ (P Q R S T : Point) (PR QS PS QR : Line),
  formTriangle P R T PR QR PS ∧
  formTriangle Q S T QS PS QR ∧
  between P T S ∧
  between Q T R ∧
  ¬ QS.intersectsLine PR →
  (△ Q:S:T).similar (△ R:P:T) :=
by
  euclid_intros
  have : ∠ P:T:R = ∠ Q:T:S := by
    euclid_apply Elements.Book1.proposition_15 P S Q R T PS QR
    euclid_finish
  have : ∠ Q:S:T = ∠ R:P:T := by
    euclid_apply Elements.Book1.proposition_29''' Q R S P QS PR PS
    euclid_finish
  euclid_finish

end UniGeo.Similarity
