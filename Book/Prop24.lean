import SystemE
import Book.Prop03
import Book.Prop04
import Book.Prop05
import Book.Prop13
import Book.Prop17
import Book.Prop19
import Book.Prop23

namespace Elements.Book1

theorem proposition_24 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c > ∠ e:d:f) →
  |(b─c)| > |(e─f)| :=
by
  euclid_intros
  euclid_apply (proposition_23' d e a b c f DE AB AC) as g'
  euclid_apply (line_from_points d g') as DG
  euclid_apply (extend_point_longer DG d g' (a─c)) as g''
  euclid_apply (proposition_3 d g'' a c DG AC) as g
  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_4 a b c d e g AB BC AC DE EG DG)
  euclid_apply (proposition_5' d g f DG FG DF)
  by_cases (d.sameSide g EF)
  · euclid_assert (∠ d:f:g > ∠ e:g:f)
    euclid_assert (∠ e:f:g > ∠ e:g:f)
    euclid_apply (proposition_19 e f g EF FG EG)
    euclid_finish
  · -- Omitted by Euclid.
    by_cases g.onLine EF
    · euclid_finish
    · euclid_apply (extend_point FG g f) as h
      -- Not clear why these are needed.
      euclid_assert ¬(g.onLine DF)
      euclid_assert ¬(e.onLine DF)
      euclid_assert (g.opposingSides e DF)
      euclid_assert h.sameSide e DF

      euclid_apply (proposition_13 d f g h DF FG)
      euclid_apply (proposition_13 e f g h EF FG)
      euclid_apply (proposition_17 d g e DG EG DE)
      euclid_apply (proposition_17 d f e DF EF DE)
      euclid_assert (∠ d:g:e < ∟ + ∟)
      euclid_assert (∠ d:f:e < ∟ + ∟)
      euclid_assert (∠ e:f:g + ∠ g:f:d + ∠ d:f:e = ∟ + ∟ + ∟ + ∟)
      euclid_assert (∠ e:f:g > ∠ e:g:f)
      euclid_apply (proposition_19 e f g EF FG EG)
      euclid_finish

end Elements.Book1
