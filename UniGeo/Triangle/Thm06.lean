import SystemE
import Book.Prop13
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_6 : ∀ (G H I J K : Point) (GK HJ GI HK : Line),
  distinctPointsOnLine G K GK ∧
  distinctPointsOnLine H J HJ ∧
  distinctPointsOnLine G I GI ∧
  distinctPointsOnLine H K HK ∧
  GK ≠ GI ∧
  HK ≠ GK ∧
  HJ ≠ HK ∧
  H.onLine GI ∧ between G H I ∧
  GI.intersectsLine HK ∧
  GI.intersectsLine HJ ∧ J.sameSide K GI ∧
  ¬ GK.intersectsLine HJ →
  ∠ H:G:K + ∠ H:K:G + ∠ G:H:K = ∟ + ∟ :=
by
  euclid_intros
  have : ∠ H:G:K = ∠ I:H:J := by
    euclid_apply Elements.Book1.proposition_29'''' J K I H G HJ GK GI
    euclid_finish
  have : ∠ G:K:H = ∠ J:H:K := by
    euclid_apply Elements.Book1.proposition_29''' J G H K HJ GK HK
    euclid_finish
  euclid_assert ∠ I:H:K = ∠ H:G:K + ∠ G:K:H
  have : ∠ G:H:K + ∠ I:H:K = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 K H I G HK GI
    euclid_finish
  euclid_finish

end UniGeo.Triangle
