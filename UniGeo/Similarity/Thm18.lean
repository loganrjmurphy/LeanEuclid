import SystemE
import Book.Prop32
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_18 : ∀ (T U V W : Point) (UV VW UW TW : Line),
  formTriangle T V W UV VW TW ∧
  formTriangle T U W UV UW TW ∧
  between U T V ∧
  ∠ V:W:U = ∟ ∧
  ∠ W:T:U = ∟ ∧ ∠ V:T:W = ∟ →
  (△ T:U:W).similar (△ T:W:V) :=
by
  euclid_intros
  -- euclid_assert ∠ U:T:W = ∠ V:T:W
  have : ∠ W:V:U + ∠ V:U:W = ∟ := by
    euclid_apply extend_point UV V U as X
    euclid_apply Elements.Book1.proposition_32 W V U X VW UV UW
    euclid_finish
  have : ∠ W:V:U + ∠ T:W:V = ∟ := by
    euclid_apply extend_point TW W T as Y
    euclid_apply Elements.Book1.proposition_32 V W T Y VW TW UV
    euclid_finish
  -- euclid_assert ∠ T:W:V = ∠ V:U:W
  euclid_finish

end UniGeo.Similarity
