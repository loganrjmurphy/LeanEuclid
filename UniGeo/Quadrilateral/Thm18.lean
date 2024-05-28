import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_18 : ∀ (E F G H : Point) (EF GH FG EH EG : Line),
  formQuadrilateral E F H G EF GH EH FG ∧
  distinctPointsOnLine E G EG ∧
  |(G─H)| = |(E─F)| ∧
  ¬ GH.intersectsLine EF →
  ∠ G:E:H = ∠ E:G:F :=
by
  euclid_intros
  have : ∠ E:G:H = ∠ F:E:G := by
    euclid_apply Elements.Book1.proposition_29''' H F G E GH EF EG
    euclid_finish
  euclid_assert (△ E:F:G).congruent (△ G:H:E)
  euclid_apply Triangle.congruent_if (△ E:F:G) (△ G:H:E)
  euclid_finish

end UniGeo.Quadrilateral
