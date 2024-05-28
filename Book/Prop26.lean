import SystemE
import Book.Prop03
import Book.Prop04
import Book.Prop16

namespace Elements.Book1

theorem proposition_26 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (∠ a:b:c = ∠ d:e:f) ∧ (∠ b:c:a = ∠ e:f:d) ∧ (|(b─c)| = |(e─f)| ∨ |(a─b)| = |(d─e)|) →
  (|(a─b)| = |(d─e)|) ∧ (|(b─c)| = |(e─f)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c = ∠ e:d:f) :=
by
  euclid_intros
  split_ors
  · have : (|(a─b)| = |(d─e)|) := by
      by_contra
      by_cases (|(a─b)| > |(d─e)|)
      · euclid_apply (proposition_3 b a e d AB DE) as g
        euclid_apply (line_from_points g c) as GC
        euclid_apply (proposition_4 b g c e d f AB GC BC DE DF EF)
        euclid_finish
      · -- Omitted by Euclid.
        euclid_assert (|(d─e)| > |(a─b)|)
        euclid_apply (proposition_3 e d b a DE AB) as g
        euclid_apply (line_from_points g f) as GF
        euclid_apply (proposition_4 e g f b a c DE GF EF AB AC BC)
        euclid_finish
    euclid_apply (proposition_4 b a c e d f AB AC BC DE DF EF)
    euclid_finish
  · have : (|(b─c)| = |(e─f)|) := by
      by_contra
      by_cases (|(b─c)| > |(e─f)|)
      · euclid_apply (proposition_3 b c e f BC EF) as h
        euclid_apply (line_from_points a h)  as AH
        euclid_apply (proposition_4 b a h e d f AB AH BC DE DF EF)
        euclid_apply (proposition_16 a c h b AC BC AH)
        euclid_finish
      · -- Omitted by Euclid.
        euclid_assert (|(e─f)| > |(b─c)|)
        euclid_apply (proposition_3 e f b c EF BC) as h
        euclid_apply (line_from_points d h) as DH
        euclid_apply (proposition_4 e d h b a c DE DH EF AB AC BC)
        euclid_apply (proposition_16 d f h e DF EF DH)
        euclid_finish
    euclid_apply (proposition_4 b a c e d f AB AC BC DE DF EF)
    euclid_finish

end Elements.Book1
