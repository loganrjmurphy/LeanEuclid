import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_16 : ∀ (T V W U X : Point) (TV TW UX VW : Line),
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine T W TW ∧
  distinctPointsOnLine U X UX ∧
  distinctPointsOnLine V W VW ∧
  TV.intersectsLine UX ∧ U.onLine TV ∧ between T U V ∧
  TW.intersectsLine UX ∧ X.onLine TW ∧ between T X W ∧
  TV.intersectsLine VW ∧
  TW.intersectsLine VW ∧
  ∠ T:U:X = ∠ T:W:V ∧
  ¬ UX.intersectsLine VW →
  ∠ U:V:W = ∠ T:W:V :=
by
  euclid_intros
  have : ∠ U:V:W = ∠ T:U:X := by
    euclid_apply Elements.Book1.proposition_29'''' X W T U V UX VW TV
    euclid_finish
  euclid_finish

end UniGeo.Parallel
