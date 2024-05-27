import SystemE
import Book.Prop23
import Book.Prop27


namespace Elements.Book1

theorem proposition_31 : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ ¬(a.onLine BC) →
  ∃ EF : Line, a.onLine EF ∧ ¬(EF.intersectsLine BC) :=
by
  euclid_intros
  euclid_apply (exists_point_between_points_on_line BC b c) as d
  euclid_apply (line_from_points a d) as AD
  euclid_apply (proposition_23' a d d a c b AD AD BC) as e
  euclid_apply (line_from_points e a) as EF
  euclid_apply (extend_point EF e a) as f
  use EF
  constructor
  . euclid_finish
  . euclid_apply (proposition_27 e c a d EF BC AD)
    euclid_finish

end Elements.Book1
