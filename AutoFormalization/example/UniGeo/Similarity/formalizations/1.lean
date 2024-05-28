import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Similarity

theorem theorem_1 : ∀ (I F J H G : Point) (FI FH GI GH : Line),
  formTriangle F I J FI FH FH ∧
  formTriangle G H J GH FH GI ∧
  between I J G ∧
  between H J F ∧
  |(G─J)|/|(I─J)|= |(H─J)|/|(F─J)|→
  (△ G:H:J).similar (△ I:F:J) :=
by
  euclid_intros
  have : ∠F:J:I = ∠G:J:H := by
    euclid_apply proposition_15 I G F H J GI FH
    euclid_finish
  euclid_finish

end UniGeo.Similarity
