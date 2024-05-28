import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Similarity

theorem theorem_3 : ∀ (I J G H F : Point) (GJ HI FG FJ : Line),
  formTriangle I H F HI GF FJ ∧
  formTriangle J G F GJ FG FJ ∧
  between J I F ∧
  between G H F ∧
  |(F─I)|/|(F─J)|= |(H─F)|/|(F─G)| →
  (△ F:H:I).similar (△ F:G:J) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Similarity
