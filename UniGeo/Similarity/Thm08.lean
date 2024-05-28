import SystemE
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_8 : ∀ (G H I J K : Point) (GH GI HI JK : Line),
  formTriangle G H I GH HI GI ∧
  formTriangle G J K GH JK GI ∧
  between G J H ∧
  between G K I ∧
  |(G─J)| / |(G─H)| = |(G─K)| / |(G─I)| →
  (△ G:J:K).similar (△ G:H:I) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Similarity
