import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_7 : ∀ (H I J K : Point) (HI JK IJ HK HJ : Line),
  formQuadrilateral H I K J HI JK HK IJ ∧
  distinctPointsOnLine H J HJ ∧
  |(J─K)| = |(H─I)| ∧
  ¬ JK.intersectsLine HI →
  ∠ H:K:J = ∠ H:I:J :=
by
  euclid_intros
  have : ∠ H:J:K = ∠ I:H:J := by
    euclid_apply Elements.Book1.proposition_29''' K I J H JK HI HJ
    euclid_finish
  euclid_assert (△ H:I:J).congruent (△ J:K:H)
  euclid_apply Triangle.congruent_if (△ H:I:J) (△ J:K:H)
  euclid_finish

end UniGeo.Quadrilateral
