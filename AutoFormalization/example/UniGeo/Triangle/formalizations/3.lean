import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Triangle

theorem theorem_3 : ∀ (R S P Q : Point) (QR PR PQ PS : Line),
  formTriangle R Q P QR PQ PR ∧
  distinctPointsOnLine P S PS ∧
  PS.intersectsLine QR ∧ S.onLine QR ∧ between R S Q ∧
  |(P─Q)| = |(P─R)| ∧
  ∠ R:P:S =  ∠ S:P:Q  →
  |(Q─S)| = |(R─S)| :=
by
  euclid_intros
  have : △P:Q:S≅△P:R:S :=by euclid_finish
  have: |(Q─S)| = |(R─S)| := by
    euclid_apply (△P:Q:S).congruent_if △P:R:S
    euclid_finish
  euclid_finish

end UniGeo.Triangle
