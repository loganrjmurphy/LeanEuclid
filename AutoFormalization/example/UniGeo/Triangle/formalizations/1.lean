import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Triangle

theorem theorem_1 : ∀ (U X V W : Point) (UV UX UW VW : Line),
  formTriangle U V W UV VW UW ∧
  distinctPointsOnLine U X UX ∧
  UX.intersectsLine VW ∧ X.onLine VW ∧ between V X W ∧
  ∠ W:U:X = ∠ V:U:X ∧
  ∠ U:X:V = ∟ ∧ ∠ U:X:W = ∟ →
   |(W─X)| = |(V─X)|:=
by
  euclid_intros
  have : ∠ U:X:V = ∠ U:X:W := by euclid_finish
  have : △U:V:X≅△U:W:X := by euclid_finish
  have : |(W─X)| = |(V─X)| := by
    euclid_apply (△U:V:X).congruent_if △U:W:X
    euclid_finish
  euclid_finish

end UniGeo.Triangle
