import SystemE
import Book.Prop31
import Book.Prop34
import Book.Prop36


namespace Elements.Book1

theorem proposition_38 : ∀ (a b c d e f: Point) (AD BF AB AC DE DF : Line),
  a.onLine AD ∧ d.onLine AD ∧ formTriangle a b c AB BF AC ∧ formTriangle d e f DE BF DF ∧
  ¬(AD.intersectsLine BF) ∧ (between b c f) ∧ (between b e f) ∧ |(b─c)| = |(e─f)| →
  Triangle.area △ a:b:c = Triangle.area △ d:e:f :=
by
  euclid_intros
  euclid_apply (proposition_31 b a c AC) as BG
  euclid_apply (intersection_lines AD BG) as g
  euclid_apply (proposition_31 f d e DE) as FH
  euclid_apply (intersection_lines AD FH) as h
  euclid_apply (proposition_36' g b c a d e f h AD BF BG AC DE FH)
  euclid_apply (proposition_34 g a b c AD BF BG AC AB)
  euclid_apply (proposition_34 e f d h BF AD DE FH DF)
  euclid_finish

end Elements.Book1
