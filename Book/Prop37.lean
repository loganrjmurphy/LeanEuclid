import SystemE
import Book.Prop31
import Book.Prop34
import Book.Prop35


namespace Elements.Book1

theorem proposition_37 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) ∧ d.sameSide c AB →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
by
  euclid_intros
  euclid_apply (proposition_31 b a c AC) as BE
  euclid_apply (intersection_lines AD BE) as e
  euclid_apply (proposition_31 c b d BD) as CF
  euclid_apply (intersection_lines AD CF) as f
  euclid_apply (proposition_35' e b c a d f AD BC BE AC BD CF)
  euclid_apply (proposition_34 e a b c AD BC BE AC AB)
  euclid_apply (proposition_34 f d c b AD BC CF BD CD)
  euclid_finish

theorem proposition_37' : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
by
  euclid_intros
  by_cases (d.sameSide c AB)
  . euclid_apply (proposition_37 a b c d AB BC AC BD CD AD)
    assumption
  . euclid_apply (proposition_37 d b c a BD BC CD AB AC AD)
    euclid_finish

end Elements.Book1
