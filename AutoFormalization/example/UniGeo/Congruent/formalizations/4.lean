import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Congruent

theorem theorem_4: ∀ (P Q R S : Point) (PQ QR RS PS PR: Line),
  formTriangle R P S PR PS RS ∧
  formTriangle P Q R PQ QR PR ∧
  S.opposingSides Q PR ∧
  ∠ S:P:R = ∠ Q:P:R ∧
  ∠ P:R:S = ∠ P:R:Q →
  (△ P:R:S).congruent (△ P:R:Q) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Congruent
