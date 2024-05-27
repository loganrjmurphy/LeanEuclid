import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_13 : ∀ (Q S T R U : Point) (QS QT ST RU : Line),
  distinctPointsOnLine Q S QS ∧
  distinctPointsOnLine Q T QT ∧
  distinctPointsOnLine S T ST ∧
  distinctPointsOnLine R U RU ∧
  QS.intersectsLine RU ∧ R.onLine QS ∧ between Q R S ∧
  QT.intersectsLine RU ∧ U.onLine QT ∧ between Q U T ∧
  QS.intersectsLine ST ∧
  QT.intersectsLine ST ∧
  ∠ Q:R:U = ∠ Q:U:R ∧
  ¬ ST.intersectsLine RU →
  ∠ R:S:T = ∠ S:T:Q :=
by
  euclid_intros
  have : ∠ U:T:S = ∠ Q:U:R := by
    euclid_apply Elements.Book1.proposition_29'''' R S Q U T RU ST QT
    euclid_finish
  have : ∠ R:S:T = ∠ Q:R:U := by
    euclid_apply Elements.Book1.proposition_29'''' U T Q R S RU ST QS
    euclid_finish
  euclid_finish

end UniGeo.Parallel
