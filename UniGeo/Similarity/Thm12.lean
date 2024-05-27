import SystemE
import Book.Prop13
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_12 : ∀ (S T U V W : Point) (ST TW SW UV : Line),
  formTriangle S T W ST TW SW ∧
  formTriangle U V W UV TW SW ∧
  between S U W ∧
  between T V W ∧
  ∠ S:T:W + ∠ T:V:U = ∟ + ∟ →
  (△ U:V:W).similar (△ S:T:W) :=
by
  euclid_intros
  have : ∠ U:V:W + ∠ T:V:U = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 U V T W UV TW
    euclid_finish
  -- euclid_assert ∠ U:V:W = ∠ S:T:V
  euclid_finish

end UniGeo.Similarity
