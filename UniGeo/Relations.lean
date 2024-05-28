import SystemE.Theory.Relations

@[simp]
abbrev twoLinesIntersectAtPoint (AB BC : Line) (b: Point) : Prop :=
  AB.intersectsLine BC ∧ b.onLine AB ∧ b.onLine BC ∧ AB ≠ BC

@[simp]
abbrev formQuadrilateral (a b c d : Point) (AB CD AC BD : Line) : Prop :=
    distinctPointsOnLine a b AB ∧
    distinctPointsOnLine c d CD ∧
    distinctPointsOnLine a c AC ∧
    distinctPointsOnLine b d BD ∧ a.sameSide c BD ∧ a.sameSide b CD ∧ b.sameSide d AC ∧ c.sameSide d AB

@[simp]
axiom quadrilateralAnglesSum (a b c d : Point) (AB CD AC BD : Line) :
    formQuadrilateral a b c d AB CD AC BD → ∠ a:b:d + ∠ b:d:c + ∠ d:c:a + ∠ c:a:b = ∟ + ∟ + ∟ + ∟

namespace Triangle

@[simp]
abbrev congruent : Triangle → Triangle →  Prop
| (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
  -- SSS
  (|(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)|) ∨
  -- SAS
  (|(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)|) ∨
  (|(B─C)| = |(E─F)| ∧ ∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)|) ∨
  (|(C─A)| = |(F─D)| ∧ ∠ C:A:B = ∠ F:D:E ∧ |(A─B)| = |(D─E)|) ∨
--  ASA or AAS
  (∠ A:B:C = ∠ D:E:F ∧ |(A─B)| = |(D─E)| ∧ ∠ B:C:A = ∠ E:F:D) ∨
  (∠ B:C:A = ∠ E:F:D ∧ |(B─C)| = |(E─F)| ∧ ∠ C:A:B = ∠ F:D:E) ∨
  (∠ C:A:B = ∠ F:D:E ∧ |(C─A)| = |(F─D)| ∧ ∠ A:B:C = ∠ D:E:F) ∨
  (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D ∧ |(B─C)| = |(E─F)|) ∨
  (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E ∧ |(C─A)| = |(F─D)|) ∨
  (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F ∧ |(A─B)| = |(D─E)|) ∨
  (∠ C:A:B = ∠ F:D:E ∧ ∠ B:C:A = ∠ E:F:D ∧ |(A─B)| = |(D─E)|) ∨
  (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)|) ∨
  (∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)| ∧ ∠ C:A:B = ∠ F:D:E)

@[aesop unsafe [apply,forward]]
axiom congruent_if (T1 T2: Triangle): congruent T1 T2 →
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(A─C)| = |(D─F)| ∧ ∠ A:B:C = ∠ D:E:F ∧ ∠ A:C:B = ∠ D:F:E ∧ ∠ B:A:C = ∠ E:D:F

notation:50 a:51 "≅" b:51 => congruent a b

@[simp]
abbrev similar (T1 T2: Triangle): Prop :=
  match T1, T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
  (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D) ∨
  (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E) ∨
  (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F) ∨
-- SAS criterion (with side ratios)
  (|(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧ ∠ A:B:C = ∠ D:E:F) ∨
  (|(B─C)| / |(E─F)| = |(C─A)| / |(F─D)| ∧ ∠ B:C:A = ∠ E:F:D) ∨
  (|(C─A)| / |(F─D)| = |(A─B)| / |(D─E)| ∧ ∠ C:A:B = ∠ F:D:E) ∨
-- SSS criterion (with side ratios)
  (|(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧ |(B─C)| / |(E─F)| = |(C─A)| / |(F─D)|)

notation:50 a:51 "~" b:51 => similar a b

@[aesop unsafe [apply,forward]]
axiom similar_if (T1 T2: Triangle): similar T1 T2 →
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    |(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧ |(A─B)| / |(D─E)| = |(B─C)| / |(E─F)|
   ∧ |(C─A)| / |(F─D)| = |(A─B)| / |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F
   ∧ ∠ A:C:B = ∠ D:F:E ∧ ∠ B:A:C = ∠ E:D:F

end Triangle
