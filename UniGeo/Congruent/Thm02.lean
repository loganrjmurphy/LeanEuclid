import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_2 : ∀ (T U V W : Point) (TU UV TV VW TW : Line),
  formTriangle T U V TU UV TV ∧
  formTriangle T V W TV VW TW ∧
  U.opposingSides W TV ∧
  |(T─U)| = |(V─W)| ∧
  ¬ TU.intersectsLine VW →
  (△ T:U:V).congruent (△ V:W:T) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' U W T V TU VW TV
  euclid_finish

end UniGeo.Congruent
