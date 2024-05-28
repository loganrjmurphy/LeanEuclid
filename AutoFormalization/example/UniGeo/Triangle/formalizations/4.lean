import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Triangle

theorem theorem_4 : ∀ (F H I G : Point) (HF GH FG FI : Line),
  formTriangle F H G HF GH FG ∧
  distinctPointsOnLine F I FI ∧
  FI.intersectsLine GH ∧ I.onLine GH ∧ between H I G ∧
   ∠ F:I:G = ∟ ∧ ∠F:I:H=∟ ∧
  |(G─I)| = |(I─H)| →
  ∠ F:H:I = ∠ F:G:I :=
by
  euclid_intros
  have : ∠F:I:G = ∠F:I:H :=by euclid_finish
  have : △F:G:I ≅ △F:H:I :=by euclid_finish
  have: ∠ F:H:I = ∠ F:G:I := by
    euclid_apply (△F:G:I).congruent_if △F:H:I
    euclid_finish
  euclid_finish

end UniGeo.Triangle
