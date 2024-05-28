import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_9 : ∀ (F G H I : Point) (FG HI GH FI FH : Line),
  formQuadrilateral F G I H FG HI FI GH ∧
  distinctPointsOnLine F H FH ∧
  ¬ HI.intersectsLine FG ∧
  ∠ H:I:F = ∟ ∧
  ∠ F:G:H = ∟ →
  |(H─I)| = |(F─G)| :=
by
  euclid_intros
  have : ∠ G:F:H = ∠ F:H:I := by
    euclid_apply Elements.Book1.proposition_29''' G I F H FG HI FH
    euclid_finish
  euclid_assert (△ F:H:I).congruent (△ H:F:G)
  euclid_apply Triangle.congruent_if (△ F:H:I) (△ H:F:G)
  euclid_finish

end UniGeo.Quadrilateral
