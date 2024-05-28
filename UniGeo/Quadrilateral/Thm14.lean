import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_14 : ∀ (G H I J : Point) (GH IJ HI GJ GI : Line),
  formQuadrilateral G H J I GH IJ GJ HI ∧
  distinctPointsOnLine G I GI ∧
  ∠ I:G:H = ∠ I:G:J ∧
  ∠ G:H:I = ∠ G:J:I →
  |(G─J)| = |(G─H)| :=
by
  euclid_intros
  euclid_assert (△ G:H:I).congruent (△ G:J:I)
  euclid_apply Triangle.congruent_if (△ G:H:I) (△ G:J:I)
  euclid_finish

end UniGeo.Quadrilateral
