import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Parallel

theorem theorem_3 : ∀ (P Q R S T : Point) (PR PS QT RS: Line),
  distinctPointsOnLine R S RS ∧
  distinctPointsOnLine Q T QT ∧
  distinctPointsOnLine P R PR ∧
  distinctPointsOnLine P S PS ∧
  QT.intersectsLine PR ∧ Q.onLine PR ∧ between P Q R ∧
  RS.intersectsLine PR ∧ T.onLine PS ∧ between P T S ∧
  QT.intersectsLine PS ∧
  RS.intersectsLine PS ∧
  ∠ P:T:Q = ∠ P:Q:T ∧ ¬ QT.intersectsLine RS → ∠ P:S:R = ∠ Q:R:S
  :=
by
  euclid_intros
  have : ∠ P:S:R = ∠ P:T:Q:=by
    euclid_apply proposition_29'''' Q R P T S QT RS PS
    euclid_finish
  have : ∠ Q:R:S = ∠ P:Q:T := by
    euclid_apply proposition_29'''' T S P Q R QT RS PR
    euclid_finish
  have : ∠ Q:R:S = ∠ P:T:Q  := by euclid_finish
  have : ∠ P:S:R = ∠ Q:R:S := by euclid_finish
  euclid_finish

end UniGeo.Parallel
