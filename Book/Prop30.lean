import SystemE
import Book.Prop27
import Book.Prop29


namespace Elements.Book1

theorem proposition_30 : ∀ (AB CD EF : Line),
  AB ≠ CD ∧ CD ≠ EF ∧ EF ≠ AB ∧ ¬(AB.intersectsLine EF) ∧ ¬(CD.intersectsLine EF) →
  ¬(AB.intersectsLine CD) :=
by
  euclid_intros
  euclid_apply (line_nonempty AB) as g
  euclid_apply (exists_distincts_points_on_line CD g) as k
  euclid_apply (line_from_points g k) as GK
  euclid_apply (intersection_lines EF GK) as h
  euclid_apply (exists_distincts_points_on_line AB g) as a
  euclid_apply (extend_point AB a g) as b
  euclid_apply (point_on_line_same_side GK EF a) as e
  euclid_apply (extend_point EF e h) as f
  euclid_apply (point_on_line_same_side GK CD a) as c
  euclid_apply (extend_point CD c k ) as d

  by_cases (between g h k)
  · euclid_apply (proposition_29'' a b f g h AB EF GK)
    euclid_apply (proposition_29' e f c d g h k EF CD GK)
    euclid_apply (proposition_27 a d g k AB CD GK)
    euclid_finish
  · -- Omitted by Euclid.
    by_cases (between g k h)
    · euclid_apply (proposition_29'' a b f g h AB EF GK)
      euclid_apply (proposition_29' c d e f g k h CD EF GK)
      euclid_apply (proposition_27 a d g k AB CD GK)
      euclid_finish
    · euclid_apply (proposition_29'' d c e k h CD EF GK)
      euclid_apply (proposition_29' b a f e k g h AB EF GK)
      euclid_apply (proposition_27 a d g k AB CD GK)
      euclid_finish

end Elements.Book1
