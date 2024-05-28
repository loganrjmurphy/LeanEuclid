import SystemE
import Book.Prop05

namespace Elements.Book1

theorem proposition_7 : ∀ (a b c d : Point) (AB AC CB AD DB : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine c b CB ∧
  distinctPointsOnLine a d AD ∧ distinctPointsOnLine d b DB ∧ (c.sameSide d AB) ∧ c ≠ d ∧
  (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|) → False :=
by
  euclid_intros
  euclid_apply (line_from_points c d) as CD
  by_cases a.sameSide b CD <;> by_cases d.sameSide b AC
  · euclid_apply (proposition_5' a c d AC CD AD)
    euclid_apply (sum_angles_onlyif d c b a CD DB)
    euclid_apply (proposition_5' b c d CB CD DB)
    euclid_apply (sum_angles_onlyif c a d b AC CD)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (proposition_5' a d c AD CD AC)
    euclid_apply (sum_angles_onlyif c d b a CD CB)
    euclid_apply (proposition_5' b d c DB CD CB)
    euclid_apply (sum_angles_onlyif d a c b AD CD)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (extend_point AC a c) as e
    euclid_apply (extend_point AD a d) as f
    euclid_apply (proposition_5 a c d e f AC CD AD)
    euclid_apply (sum_angles_onlyif c e d b AC CD)
    euclid_apply (proposition_5' b c d CB CD DB)
    euclid_apply (sum_angles_onlyif d c b f CD DB)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (extend_point AC a c) as e
    euclid_apply (extend_point AD a d) as f
    euclid_apply (proposition_5 a c d e f AC CD AD)
    euclid_apply (sum_angles_onlyif d f c b AD CD)
    euclid_apply (proposition_5' b d c DB CD CB)
    euclid_apply (sum_angles_onlyif c d b e CD CB)
    euclid_finish

end Elements.Book1
