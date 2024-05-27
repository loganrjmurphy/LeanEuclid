import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_4 : ∀ (G H I J : Point) (GH IJ HI GJ GI : Line),
  formQuadrilateral G H J I GH IJ GJ HI ∧
  distinctPointsOnLine G I GI ∧
  |(I─J)| = |(G─H)| ∧
  ¬ GH.intersectsLine IJ →
  |(H─I)| = |(G─J)| :=
by
  euclid_intros
  have : ∠ G:I:J = ∠ H:G:I := by
    euclid_apply Elements.Book1.proposition_29''' H J G I GH IJ GI
    euclid_finish
  euclid_assert (△ G:H:I).congruent (△ I:J:G)
  euclid_apply Triangle.congruent_if (△ G:H:I) (△ I:J:G)
  euclid_finish

end UniGeo.Quadrilateral
