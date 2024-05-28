import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_2 : ∀ (E F G H : Point) (EF GH FG EH EG : Line),
  formQuadrilateral E F H G EF GH EH FG ∧
  distinctPointsOnLine E G EG ∧
  ¬ GH.intersectsLine EF ∧
  |(E─F)| = |(G─H)| →
  ∠ E:F:G = ∠ E:H:G :=
by
  euclid_intros
  have : ∠ E:G:H = ∠ F:E:G := by
    euclid_apply Elements.Book1.proposition_29''' H F G E GH EF EG
    euclid_finish
  euclid_assert (△ E:F:G).congruent (△ G:H:E)
  euclid_apply Triangle.congruent_if (△ E:F:G) (△ G:H:E)
  euclid_finish

end UniGeo.Quadrilateral
