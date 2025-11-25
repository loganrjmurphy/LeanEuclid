import SystemE.Theory.Relations


-- ********
-- Diagrammatic inferences defined in Sec 3.4 of Avigad et al  2009
-- Generally speaking, they are not used explicitly in the tactics written by humans.
-- ********

-- Part I : Generalities

/--
If points `a` and `b` are distinct, and both points are on lines `L` and `M`, then `L = M`
-/
axiom two_points_determine_line :
  ∀ (a b : Point) (L M : Line), distinctPointsOnLine a b L ∧ (a.onLine M) ∧ (b.onLine M) → L = M

/--
If points `a` and `b` are both centers of `(α : Circle)` then `a = b`
-/
axiom centre_unique :
  ∀ (a b : Point) (α : Circle), (a.isCentre α) ∧ (b.isCentre α) → a = b

-- ********
-- 3
-- If a is the centre of α then a is inside α
-- ********

axiom center_inside_circle : ∀ (a : Point) (α : Circle),
  a.isCentre α → a.insideCircle α

-- ********
-- 4
-- If (a : Point) is inside (α : Circle), then a is not on α
-- -- ********
axiom inside_not_on_circle : ∀ (a : Point) (α : Circle),
  a.insideCircle α → ¬(a.onCircle α)

-- ********  between axioms ********

-- ********
-- 1
-- If b is  between a and c then b is  between c and a, a != b, a != c, and a is
-- not a. between bnd c
-- ********
axiom between_symm : ∀ (a b c : Point), between a b c →
  (between c b a) ∧ (a ≠ b) ∧ (a ≠ c) ∧ ¬(between b a c)

-- ********
-- 2
-- If b is  between a and c, a is on L, and b is on L, then c is on L
-- ********

axiom between_same_line_out : ∀ (a b c : Point) (L : Line),
  (between a b c) ∧ (a.onLine L) ∧ (b.onLine L) →
  c.onLine L

-- ********
-- 3  If b is  between a and c, a is on L, and c is on L, then b is on L
-- ********

axiom between_same_line_in : ∀ (a b c : Point) (L : Line),
  (between a b c) ∧ (a.onLine L) ∧ (c.onLine L) →
  b.onLine L

-- -- ********
-- 4
-- If b is  between a and c and d is  between a and b then d is  between a and c
-- -- ********
axiom between_trans_in : ∀ (a b c d : Point),
  (between a b c) ∧ (between a d b) → between a d c

-- ********
-- 5
-- If b is  between a and c and c is a. between bnd d then b is  between a and d
-- ********

-- -- ********
axiom between_trans_out : ∀ (a b c d : Point),
  (between a b c) ∧ (between b c d) → (between a b d)

-- ********
-- 6
-- If a, b, and c are distinct points on a line L, then then either b is  between
-- a and c, or a is a. between bnd c, or c is  between a and b
-- ********

axiom between_points : ∀ (a b c : Point) (L : Line),
  (a ≠ b) ∧ (b ≠ c) ∧ (c ≠ a) ∧ (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) →
  (between a b c) ∨ (between b a c) ∨ (between a c b)

-- ********
-- 7
-- If b is  between a and c and b is  between a and d then b is not  between c
-- and d
-- ********
axiom between_not_trans : ∀ (a b c d : Point),
  (between a b c) ∧ (between a b d) → ¬(between c b d)

-- ******** same side axioms ********

-- ********
-- 1
-- If a is not on L, then a and a are on the same side of L
-- ********
axiom same_side_rfl : ∀ (a : Point) (L : Line),
  ¬(a.onLine L) → a.sameSide a L

-- ********
-- 2
-- If a and b are on the same side of L, then b and a are on the same side of L
-- ********
axiom same_side_symm : ∀ (a b : Point) (L : Line),
  a.sameSide b L → b.sameSide a L

-- ********
-- 3
-- If a and b are on the same side of L, then a is not on L
-- ********
axiom same_side_not_on_line : ∀ (a b : Point) (L : Line),
  a.sameSide b L → ¬(a.onLine L)

-- ********
-- 4
-- If a and b are on the same side of L, and a and c are on the same side of
-- L, then b and c are on the same side of L
-- -- ********
axiom same_side_trans : ∀ (a b c : Point) (L : Line),
  (a.sameSide b L) ∧ (a.sameSide c L) → b.sameSide c L

-- ********
-- 5
-- If a, b, and c are not on L, and a and b are not on the same side of L,
-- then either a and c are on the same side of L, or b and c are on the same
-- side of L
-- ********
axiom same_side_pigeon_hole : ∀ (a b c : Point) (L : Line),
  ¬(a.onLine L) ∧ ¬(b.onLine L) ∧ ¬(c.onLine L) →
  (a.sameSide b L) ∨ (a.sameSide c L) ∨ (b.sameSide c L)

-- ********
-- 1
-- If b is  between a and c and a and c are on the same side of L, then a and
-- b are on the same side of L
-- ********
axiom pasch_1: ∀ (a b c : Point) (L : Line),
  (between a b c) ∧ (a.sameSide c L) → a.sameSide b L

-- ********
-- 2
-- If b is  between a and c and a is on L and b is not on L, then b and c are
-- on the same side of L
-- -- ********
axiom pasch_2: ∀ (a b c : Point) (L : Line),
  (between a b c) ∧ (a.onLine L) ∧ ¬(b.onLine L) →
  b.sameSide c L

-- ********
-- 3
-- If b is  between a and c and b is on L then a and c are not on the same
-- side of L
-- ********
-- -- See also Avigad's notes on this rule (https://www.andrew.cmu.edu/user/avigad/Papers/euclid_notes.htm)
axiom pasch_3: ∀ (a b c : Point) (L : Line),
  (between a b c) ∧ (b.onLine L) → ¬(a.sameSide c L)

-- ********
-- 4
-- If b is the intersection of distinct lines L and M, a and c are distinct points
-- on M, a != b, c != b, and a and c are not on the same side of L, then b is
--  between a and c
-- ********

axiom pasch_4: ∀ (a b c : Point) (L M : Line),
  (L ≠ M) ∧ (b.onLine L) ∧ (b.onLine M) ∧ distinctPointsOnLine a c M ∧
  (a ≠ b) ∧ (c ≠ b) ∧ ¬(a.sameSide c L) →
  between a b c

-- ******** triple incidence axioms ********

-- ********
-- 1
-- If L, M, and N are lines meeting at a point a, and b, c, and d are points
-- on L, M, and N respectively, and if c and d are on the same side of L,
-- and b and c are on the same side of N, then b and d are not on the same
-- side of M
-- ********
axiom triple_incidence_1 : ∀ (L M N : Line) (a b c d : Point),
  (a.onLine L) ∧ (a.onLine M) ∧ (a.onLine N) ∧ (b.onLine L) ∧
  (c.onLine M) ∧ (d.onLine N) ∧ (c.sameSide d L) ∧ (b.sameSide c N) →
  ¬(b.sameSide d M)

-- ********
-- 2
-- If L, M, and N are lines meeting at a point a, and b, c, and d are points
-- on L, M, and N respectively, and if c and d are on the same side of L,
-- and b and d are not on the same side of M, and d is not on M and b != a,
-- then b and c are on the same side of N
-- ********
axiom triple_incidence_2 : ∀ (L M N : Line) (a b c d : Point),
  (a.onLine L) ∧ (a.onLine M) ∧ (a.onLine N) ∧ (b.onLine L) ∧
  (c.onLine M) ∧ (d.onLine N) ∧ (c.sameSide d L) ∧ ¬(b.sameSide d M) ∧ ¬(d.onLine M) ∧ (b ≠ a) →
  b.sameSide c N

-- ********
-- 3
-- If L, M, and N are lines meeting at a point a, and b, c, and d are points
-- on L, M, and N respectively, and if c and d are on the same side of L,
-- and b and c are on the same side of N, and d and e are on the same side
-- of M, and c and e are on the same side of N, then c and e are on the same
-- side of L
-- ********
axiom triple_incidence_3 : ∀ (L M N : Line) (a b c d e : Point),
  (a.onLine L) ∧ (a.onLine M) ∧ (a.onLine N) ∧ (b.onLine L) ∧
  (c.onLine M) ∧ (d.onLine N) ∧ (c.sameSide d L) ∧ (b.sameSide c N) ∧
  (d.sameSide e M) ∧ (c.sameSide e N) →
  c.sameSide e L

-- ******** circle axioms ********

-- ********
-- 1
-- If a, b, and c are on L, a is inside α, b and c are on α, and b != c, then a
-- -- is a. between bnd c
-- -- ********
axiom circle_line_intersections : ∀ (a b c : Point) (L : Line) (α : Circle),
  (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) ∧
  (a.insideCircle α) ∧ (b.onCircle α) ∧ (c.onCircle α) ∧ (b ≠ c) →
  between b a c

-- ********
-- 2
-- If a and b are each inside α or on α, and c is  between a and b, then c is
-- inside α
-- ********

axiom circle_points_between : ∀ (a b c : Point) (α : Circle),
  ¬(a.outsideCircle α) ∧ ¬(b.outsideCircle α) ∧ (between a c b) →
  c.insideCircle α

-- ********
-- 3
-- If a is inside α or on α, c is not inside α, and c is  between a and b, then b
-- is neither inside α nor on α
-- ********
axiom circle_points_extend : ∀ (a b c : Point) (α : Circle),
  ¬(a.outsideCircle α) ∧ ¬(c.insideCircle α) ∧ (between a c b) →
  (b.outsideCircle α)

-- ********
-- 4  Let α and β be distinct circles that intersect in distinct points c and d
-- Let a be a the centre of α, let b be the centre of β, and let L be the line
-- through a and b  Then c and d are not on the same side of L
-- ********

axiom circles_intersections_diff_side : ∀ (a b c d : Point) (α β : Circle) (L : Line),
  (α ≠ β) ∧ (c.onCircle α) ∧ (c.onCircle β) ∧ (d.onCircle α) ∧
  (d.onCircle β) ∧ (c ≠ d) ∧ (a.isCentre α) ∧ (b.isCentre β) ∧
  (a.onLine L) ∧ (b.onLine L) → ¬(c.sameSide d L)

-- ******** intersection rules ********

-- ********
-- 1
-- If a and b are on different sides of L, and M is the line through a and b,
-- then L and M intersect
-- ********
axiom intersection_lines_opposing: ∀ (a b : Point) (L M : Line),
  (a.opposingSides b L) ∧ (a.onLine M) ∧ (b.onLine M) →
  L.intersectsLine M

-- /--
-- Not in [Avigad et al., 2009]
-- -/
axiom intersection_lines_common_point : ∀ (a : Point) (L M : Line),
  a.onLine L ∧ a.onLine M ∧ L ≠ M →
  L.intersectsLine M

-- /--
-- Not in [Avigad et al., 2009]
-- -/
axiom parallel_line_unique : ∀ (a : Point) (L M N : Line),
  ¬(a.onLine L) ∧ a.onLine M ∧ a.onLine N ∧ ¬(L.intersectsLine M) ∧ ¬(L.intersectsLine N) →
   M = N

-- /--
-- Not in [Avigad et al., 2009]
-- -/

axiom intersection_symm :
  ∀ (L M : Line), L.intersectsLine M → L.intersectsLine L

-- ********
-- 2
-- If a is on or inside α, b is on or inside α, and a and b are on different sides
-- of L, then L and α intersect
-- ********
axiom intersection_circle_line_1: ∀ (a b : Point) (α : Circle) (L: Line),
  ¬(a.outsideCircle α) ∧ ¬(b.outsideCircle α) ∧ (a.opposingSides b L) →
  L.intersectsCircle α

-- ********
-- 3  If a is inside α and on L, then L and α intersect
-- ********
axiom intersection_circle_line_2: ∀ (a : Point) (α : Circle) (L: Line),
  (a.insideCircle α) ∧ (a.onLine L) → L.intersectsCircle α

-- ********
-- 4  If a is on or inside α, b is on or inside α, a is inside β, and b is outside β,
-- then α and β intersect
-- ********

axiom intersection_circle_circle_1: ∀ (a b : Point) (α β : Circle),
  (a.onCircle α) ∧ ¬(b.outsideCircle α) ∧ (a.insideCircle β) ∧ (b.outsideCircle β) →
   α.intersectsCircle β

-- ********
-- 5  If a is on α, b is in α, a is in β, and b is on β, then α and β intersect
-- ********
axiom intersection_circle_circle_2: ∀ (a b : Point) (α β : Circle),
  (a.onCircle α) → (b.insideCircle α) → (a.insideCircle β) → (b.onCircle β) →
  α.intersectsCircle β

-- ******** parallelogram rules ********
-- /--
-- Not in [Avigad et al., 2009]
-- -/
axiom parallelogram_same_side : ∀ (a b c d : Point) (AB CD AC BD : Line),
  formParallelogram a b c d AB CD AC BD →
  b.sameSide d AC ∧ c.sameSide d AB ∧ a.sameSide b CD
