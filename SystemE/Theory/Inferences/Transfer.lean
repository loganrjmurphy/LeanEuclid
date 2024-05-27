import SystemE.Theory.Sorts
import SystemE.Theory.Relations


--
-- Transfer inferences defined in Sec. 3.6 of Avigad et al. 2009
--
--    diagram-segment transfer axioms

--
-- 1.
-- If b is  between a and c, then ab + bc = ac.
-- [between_if, equal_circles, point_on_circle_if, point_on_circle_onlyif, sum_angles_if, sum_angles_onlyif, perpendicudlar_if, sum_areas_if]

-- Given any points a, b and c such that b is between a and c, then the straight-line from a to c is equal to the sum of the straight-lines from a to b and from b to c.
axiom between_if : ∀ (a b c : Point),
  between a b c → |(a─b)| + |(b─c)| = |(a─c)|

--
-- 2.
-- If a is the centre of α and β, b is on α, c is on β, and ab = ac, then α = β.


-- If a point x is the centre of two circles C and D, and given points b and d such that b is on C and c is on D and the straight-line from x to b is equal to the straight-line from x to c, then C is equal to D.
axiom equal_circles : ∀ (a b c : Point) (α β : Circle),
  (a.isCentre α) ∧ (a.isCentre β) ∧ (b.onCircle α) ∧ (c.onCircle β) ∧ |(a─b)| = |(a─c)| → α = β

--
-- 3.
-- If a is the centre of α and b is on α, then ac = ab if and only if c is on α.


-- If a point x is the centre of circle C and a point b is on C, then given some point c such that the straight-line from x to c is equal to the straight-line from x to b, then c is on C.
axiom point_on_circle_if : ∀ (a b c : Point) (α : Circle),
  (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─c)| = |(a─b)| → c.onCircle α

@[aesop unsafe 80% [forward, apply]]
-- If a point x is the centre of circle C and a point b is on C, then given some point c on C, the straight-line from x to c is equal to the straight-line from x to b
axiom point_on_circle_onlyif : ∀ (a b c : Point) (α : Circle),
  (a.isCentre α) ∧ (b.onCircle α) ∧ (c.onCircle α) → |(a─c)| = |(a─b)|

--
-- 4.
-- If a is the centre of α and b is on α, and ac < ab if and only if c is in α.
--
-- -- Given any points b and c, and circle C, such that b is on C and the straight-line from the centre of C to c is less than the straight-line from the centre of C to b, then c is inside the circle C.
axiom point_in_circle_if : ∀ (a b c : Point) (α : Circle),
  (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─c)| < |(a─b)| → c.insideCircle α

--
-- -- Given any points b and c, and circle C, such that b is on C and c is inside the circle C, then the straight-line from the centre of C to c is less than the straight-line from the centre of C to b.
axiom point_in_circle_onlyif : ∀ (a b c : Point) (α : Circle),
  (a.isCentre α) ∧ (b.onCircle α) ∧ (c.insideCircle α) → |(a─c)| < |(a─b)|

--    diagram-angle transfer axioms

--
-- 1.
-- Suppose a != b, a != c, a is on L, and b is on L. Then c is on L and a is
-- not  between b and c if and only if \bac = 0.
--
-- Given points a, b and c such that a is not equal to b and a is not equal to c, and line L such that a, b, and c are all on L, and a is not between b and c, then the angle bac has degree zero.
axiom degenerated_angle_if : ∀ (a b c : Point) (L : Line),
  (a ≠ b) ∧ (a ≠ c) ∧ (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) ∧ ¬(between b a c) → ∠ b:a:c = 0

-- Given points a, b and c such that a is not equal to b and a is not equal to c, and line L such that a and b are on L, and the angle formed by b:a:c has degree zero,  then c is on L and a is not between b and c.
axiom degenerated_angle_onlyif : ∀ (a b c : Point) (L : Line),
  (a ≠ b) ∧ (a ≠ c) ∧ (a.onLine L) ∧ (b.onLine L) ∧ (∠ b:a:c = 0)  → (c.onLine L) ∧ ¬(between b a c)
--
-- -- Given points a, b and c such that a is not equal to b and a is not equal to c, and line L such that a and b are on L, and the angle formed by b:a:c has degree zero,  then c is on L and a is not between b and c.
-- axiom degenerated_angle_onlyif : ∀ (a b c : Point) (L : Line),
--   (a ≠ b) ∧ (a ≠ c) ∧ (a.onLine L) ∧ (b.onLine L) ∧ (∠ b: a: c) = (0 : ℝ) → (c.onLine L) ∧ ¬(between b a c)

-- --
-- 2.
-- Suppose a is on L and M, b is on L, c is on M, a != b, a != c, d is not on
-- L or M, and L != M. Then \bac = \bad + \dac if and only if b and d
-- are on the same side of M and c and d are on the same side of L.
--

-- Given point on a given lines L and M, point b  on L, and point c on M with a distinct from b, a distinct from c, point d  not on L or M, and L distinct from M, then the angle bac is equal to the sum of angles bad and dac only if b and d are on the same side of M and c and d are on the same side of L.
-- Kaiyu: Jeremy's typo here.
axiom sum_angles_if : ∀ (a b c d : Point) (L M : Line),
  (a.onLine L) ∧ (a.onLine M) ∧ (b.onLine L) ∧ (c.onLine M) ∧ (a ≠ b) ∧ (a ≠ c) ∧
  ¬(d.onLine L) ∧ ¬(d.onLine M) ∧ (L ≠ M) ∧ (∠ b:a:c) = (∠ b:a:d) + (∠ d:a:c) →
  (b.sameSide d M) ∧ (c.sameSide d L)


-- Given point on a given lines L and M, point b  on L, and point c on M with a distinct from b, a distinct from c, point d  not on L or M, and L distinct from M, then b and d are on the same side of M and c and d are on the same side of L only if the angle bac is equal to the sum of angles bad and dac
axiom sum_angles_onlyif : ∀ (a b c d : Point) (L M : Line),
(a.onLine L) ∧ (a.onLine M) ∧ (b.onLine L) ∧ (c.onLine M) ∧ (a ≠ b) ∧ (a ≠ c) ∧
¬(d.onLine L) ∧ ¬(d.onLine M) ∧ (L ≠ M) ∧ (b.sameSide d M) ∧ (c.sameSide d L) →
(∠ b:a:c) = (∠ b:a:d) + (∠ d:a:c)

--
-- 3.
-- Suppose a and b are points on L, c is  between a and b, and d is not on L.
-- Then \acd = \dcb if and only if \acd is equal to right-angle.
--

-- Given points a and b both lying on a given line L, and point c lying between a and b, and point d not on L such that the angle acd is equal to the angle dcb, then the angle acd is a right angle.
axiom perpendicular_if : ∀ (a b c d : Point) (L : Line),
  (a.onLine L) ∧ (b.onLine L) ∧ (between a c b) ∧ ¬(d.onLine L) ∧ (∠ a:c:d = ∠ d:c:b) →
  ∠ a:c:d = ∟

-- Given points a and b both lying on a given line L, and point c lying between a and b, and point d not on L such that the angle acd is a right angle, then the angle acd is equal to the angle dcb.
axiom perpendicular_onlyif : ∀ (a b c d : Point) (L : Line),
  (a.onLine L) ∧ (b.onLine L) ∧ (between a c b) ∧ ¬(d.onLine L) ∧ (∠ a:c:d = ∟) →
  ∠ a:c:d = ∠ d:c:b

-- Given points a b and c with a distinct from b and b distinct from c, such that angle abc is the sum of two right angles, then b is between a and c
-- /--
-- Not in [Avigad et al., 2009]
-- -/
--
axiom flat_angle_if : ∀ (a b c : Point),
  a ≠ b ∧ b ≠ c ∧ ∠ a:b:c = ∟ + ∟ → between a b c

-- Given points a b and c with b between a and c, then the angle abc is the sum of two right angles

/--
Not in [Avigad et al., 2009]
-/
--
axiom flat_angle_onlyif : ∀ (a b c : Point),
  between a b c → ∠ a:b:c = ∟ + ∟


--
-- 4.
-- Suppose a, b, and b′ are on L, a, c, and c′ are on M, b != a, b′ != a, c != a,
-- c′ != a, a is not  between b and b′, and a is not between c and c′. Then
-- \bac = \b′ac′.
--

--
-- -- Given points a, b, and b′ all on a given line L, and points c, c' such that a, c, and c′ are all on given line M, with b distinct from a, b′ distinct from a, c distinct from a, c' distinct from a, a is not  between b and b′, and a is not between c and c′, then angle bac is equal to angle b′ac′.
axiom equal_angles : ∀ (a b b' c c' : Point) (L M : Line),
  (a.onLine L) ∧ (b.onLine L) ∧ (b'.onLine L) ∧ (a.onLine M) ∧ (c.onLine M) ∧ (c'.onLine M) ∧
  (b ≠ a) ∧ (b' ≠ a) ∧ (c ≠ a) ∧ (c' ≠ a) ∧ ¬(between b a b') ∧ ¬(between c a c') →
  (∠ b:a:c = ∠ b':a:c')

-- 5.
-- Suppose a and b are on L, b and c are on M, and c and d are on N. Suppose
-- also that b != c, a and d are on the same side of M, and \abc + \bcd <
-- right-angle + right-angle. Then L and N intersect, and if e is on L and
-- N, then e and a are on the same side of M.
--
--
-- -- Given lines a,b,c and d such that a and b are both on a given line L, b and c are both on a given line M, c and d are both on a given line N, b is distinct from c, a and d are on the same side of M, and the sum of angles abc and bcd is less than the sum of two right angles, then there is a point e such that e is on L and N and e is on the same side of M as a.
axiom lines_intersect : ∀ (a b c d : Point) (L M N : Line),
  (a.onLine L) ∧ (b.onLine L) ∧ (b.onLine M) ∧ (c.onLine M) ∧ (c.onLine N) ∧ (d.onLine N) ∧
  (b ≠ c) ∧ (a.sameSide d M) ∧ (∠ a:b:c) + (∠ b:c:d) < ∟ + ∟ →
  ∃ e : Point, (e.onLine L) ∧ (e.onLine N) ∧ (e.sameSide a M)

--    diagram-area transfer axioms

--
-- If a and b are on L and a != b, then △abc = 0 if and only if c is on L.
--
-- If a and b are two distinct points both lying on a given line L, with a given a point c such that the area of the triangle abc is zero, then c must also be on L.
axiom degenerated_area_if : ∀ (a b c : Point) (L : Line),
  distinctPointsOnLine a b L ∧ (Triangle.area △ a:b:c) = 0 →
  c.onLine L

-- If a and b are two distinct points both lying on a given line L, with a given a point c also lying on L, then the area of the triangle abc is zero
axiom degenerated_area_onlyif : ∀ (a b c : Point) (L : Line),
  distinctPointsOnLine a b L ∧ (c.onLine L) →
  (Triangle.area △ a:b:c) = 0


-- If a, b, c are all on a given line point L and distinct from one another, and d is not on L, and  c is  between a and b, then the sum of the areas of triangles acd and dcb is equal to the area of triangle adb
axiom sum_areas_if : ∀ (a b c d : Point) (L : Line),
  (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ ¬(d.onLine L) ∧ (between a c b) →
  (Triangle.area △ a:c:d + Triangle.area △ d:c:b = Triangle.area △ a:d:b)

-- If a, b, c are all on a given line point L and distinct from one another, and d is not on L, and the sum of the areas of triangles acd and dcb is equal to the area of triangle adb, then c is between a and b.
axiom sum_areas_onlyif : ∀ (a b c d : Point) (L : Line),
  (a.onLine L) ∧ (b.onLine L) ∧ (c.onLine L) ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ ¬(d.onLine L) ∧
  (Triangle.area △ a:c:d + Triangle.area △ d:c:b = Triangle.area △ a:d:b) →
  between a c b

--    parallelogram rules

/--
Not in [Avigad et al., 2009]
-/
-- Given a parallelogram formed from points a, b, c and d, the sum of the areas of the triangles acd and adb is equal to the sum of the areas of triangles bac and bcd
axiom parallelogram_area : ∀ (a b c d : Point) (AB CD AC BD : Line), formParallelogram a b c d AB CD AC BD →
  Triangle.area △ a:c:d + Triangle.area △ a:d:b = Triangle.area △ b:a:c + Triangle.area △ b:c:d

-- /--
-- Not in [Avigad et al., 2009]
-- -/
--
-- Given a parallelogram formed from points a, b, c and d, and given points e and f such that e is betwen a and b and f is between c and d, then the sum of the areas of the triangles acf, afe, efd, and edb is equal to the sum of the areas of triangles acd and adb
axiom sum_parallelograms_area : ∀ (a b c d e f : Point) (AB CD AC BD : Line),
  formParallelogram a b c d AB CD AC BD ∧ between a e b ∧ between c f d →
  Triangle.area △ a:c:f + Triangle.area △ a:f:e + (Triangle.area △ e:f:d) + (Triangle.area △ e:d:b) = (Triangle.area △ a:c:d) + (Triangle.area △ a:d:b)


/--
Not in [Avigad et al., 2009] but required by Proposition 47
-/
axiom rectangle_area : ∀ (a b c d : Point) (AB CD AC BD : Line),
  formParallelogram a b c d AB CD AC BD ∧ (∠ a:c:d = ∟) →
  (Triangle.area △ a:c:d + Triangle.area △ a:b:d = |(a─b)| * |(a─c)|) ∧ (Triangle.area △ b:a:c + Triangle.area △ b:d:c) = |(a─b)| * |(a─c)|
