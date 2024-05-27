import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_13 : ∀ (G H I J K : Point) (GI GJ JH HK KI : Line),
  formTriangle G J H GJ JH GI ∧
  formTriangle H K I HK KI GI ∧
  between G H I ∧
  J.sameSide K GI ∧
  |(G─J)| = |(H─K)| ∧
  ∠ H:K:I = ∠ G:J:H ∧
  ¬ GJ.intersectsLine HK →
  (△ H:I:K).congruent (△ G:H:J) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29'''' K J I H G HK GJ GI
  euclid_finish

end UniGeo.Congruent
