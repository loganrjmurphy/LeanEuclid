import SystemE

namespace Elements

theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
by
  euclid_intros
  euclid_apply circle_from_points a b as BCD
  euclid_apply circle_from_points b a as ACE
  euclid_apply intersection_circles BCD ACE as c
  euclid_apply point_on_circle_onlyif a b c BCD
  euclid_apply point_on_circle_onlyif b a c ACE
  use c
  euclid_finish

theorem proposition_1' : ∀ (a b x : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
by
  euclid_intros
  euclid_apply circle_from_points a b as BCD
  euclid_apply circle_from_points b a as ACE
  euclid_apply intersection_opposite_side BCD ACE x a b AB as c
  euclid_apply point_on_circle_onlyif a b c BCD
  euclid_apply point_on_circle_onlyif b a c ACE
  use c
  euclid_finish

theorem proposition_2 : ∀ (a b c : Point) (BC : Line),
  (distinctPointsOnLine b c BC) ∧ (a ≠ b) →
  ∃ l : Point, |(a─l)| = |(b─c)| :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (proposition_1 a b AB) as d
  euclid_apply (line_from_points d a ) as AE
  euclid_apply (line_from_points d b ) as BF
  euclid_apply (circle_from_points b c) as CGH
  euclid_apply (intersection_circle_line_extending_points CGH BF b d) as g
  euclid_apply (circle_from_points d g) as GKL
  euclid_apply (intersection_circle_line_extending_points GKL AE a d) as l
  euclid_apply (point_on_circle_onlyif b c g CGH)
  euclid_apply (point_on_circle_onlyif d l g GKL)
  euclid_apply (between_if l a d )
  euclid_apply (between_if g b d )
  use l
  euclid_finish

/-
An extension of proposition_2 to the case where a and b may be the same point.
-/
theorem proposition_2' : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC →
  ∃ l : Point, |(a─l)| = |(b─c)| :=
by
  euclid_intros
  by_cases (a = b)
  . use c
    euclid_finish
  . euclid_apply proposition_2 a b c BC as l
    use l

theorem proposition_3 : ∀ (a b c₀ c₁ : Point) (AB C : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c₀ c₁ C ∧ |(a─b)| > |(c₀─c₁)| →
  ∃ e : Point, between a e b ∧ |(a─e)| = |(c₀─c₁)| :=
by
  euclid_intros
  euclid_apply (proposition_2' a c₀ c₁ C) as d
  euclid_apply (circle_from_points a d) as DEF
  euclid_apply (intersection_circle_line_between_points DEF AB a b) as e
  euclid_apply (point_on_circle_onlyif a d e)
  use e
  euclid_finish

theorem proposition_4 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ (∠ b:a:c = ∠ e:d:f) →
  |(b─c)| = |(e─f)| ∧ (∠ a:b:c = ∠ d:e:f) ∧ (∠ a:c:b = ∠ d:f:e) :=
by
  euclid_intros
  euclid_apply (superposition a b c d e f AB BC AC DE) as (b', c', BC', DC')
  euclid_assert b' = e
  euclid_assert ∠ e:d:c' = ∠ e:d:f
  euclid_assert DC' = DF
  euclid_assert c' = f
  euclid_finish

theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB b d (c─e)) as f
  euclid_apply (proposition_3 a e f a AC AB) as g
  euclid_apply (line_from_points c f) as FC
  euclid_apply (line_from_points b g) as GB
  euclid_apply (proposition_4 a f c a g b AB FC AC AC GB AB)
  euclid_apply (proposition_4 f b c g c b AB BC FC AC BC GB)
  euclid_apply (sum_angles_onlyif b a g c AB GB)
  euclid_apply (sum_angles_onlyif c a f b AC FC)
  euclid_finish

/--
A restriction of proposition_5.
-/
theorem proposition_5' : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) →
  (∠ a:b:c = ∠ a:c:b) :=
by
  euclid_intros
  euclid_apply (extend_point AB a b) as d
  euclid_apply (extend_point AC a c) as e
  euclid_apply (proposition_5 a b c d e AB BC AC)
  euclid_finish

theorem proposition_6 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| :=
by
  euclid_intros
  by_contra
  by_cases |(a─b)| > |(a─c)|
  . euclid_apply (proposition_3 b a a c AB AC) as d
    euclid_apply (line_from_points d c) as DC
    euclid_apply proposition_4 b d c c a b AB DC BC AC AB BC
    euclid_finish
  . euclid_apply (proposition_3 c a a b AC AB) as d
    euclid_apply (line_from_points d b) as DB
    euclid_apply (proposition_4 c d b b a c AC DB BC AB AC BC)
    euclid_finish

theorem proposition_7 : ∀ (a b c d : Point) (AB AC CB AD DB : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine c b CB ∧
  distinctPointsOnLine a d AD ∧ distinctPointsOnLine d b DB ∧ (c.sameSide d AB) ∧ c ≠ d ∧
  (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|) → False :=
by
  euclid_intros
  euclid_apply (line_from_points c d) as CD
  by_cases a.sameSide b CD <;> by_cases d.sameSide b AC
  · euclid_apply (proposition_5' a c d AC CD AD)
    euclid_apply (sum_angles_onlyif d c b a CD DB)
    euclid_apply (proposition_5' b c d CB CD DB)
    euclid_apply (sum_angles_onlyif c a d b AC CD)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (proposition_5' a d c AD CD AC)
    euclid_apply (sum_angles_onlyif c d b a CD CB)
    euclid_apply (proposition_5' b d c DB CD CB)
    euclid_apply (sum_angles_onlyif d a c b AD CD)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (extend_point AC a c) as e
    euclid_apply (extend_point AD a d) as f
    euclid_apply (proposition_5 a c d e f AC CD AD)
    euclid_apply (sum_angles_onlyif c e d b AC CD)
    euclid_apply (proposition_5' b c d CB CD DB)
    euclid_apply (sum_angles_onlyif d c b f CD DB)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (extend_point AC a c) as e
    euclid_apply (extend_point AD a d) as f
    euclid_apply (proposition_5 a c d e f AC CD AD)
    euclid_apply (sum_angles_onlyif d f c b AD CD)
    euclid_apply (proposition_5' b d c DB CD CB)
    euclid_apply (sum_angles_onlyif c d b e CD CB)
    euclid_finish

theorem proposition_8 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| →
  ∠ b:a:c = ∠ e:d:f :=
by
    euclid_intros
    euclid_apply (superposition b c a e f d BC AC AB EF) as (c', g, CG', EG)
    euclid_assert c' = f
    by_cases d = g
    · euclid_finish
    · euclid_apply (proposition_7 e f d g EF DE DF EG CG')
      euclid_finish

theorem proposition_9 : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, f ≠ a ∧ (∠ b:a:f = ∠ c:a:f) :=
by
  euclid_intros
  euclid_apply point_between_points_shorter_than AB a b (a─c) as d
  euclid_apply (proposition_3 a c a d AC AB) as e
  euclid_apply (line_from_points d e) as DE
  euclid_apply (proposition_1' d e a DE) as f
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points a f) as AF
  use f
  have : ¬(f.onLine AB) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f d e AB DE FE)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  have : ¬(f.onLine AC) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f e d AC DE FD)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  euclid_apply (proposition_8 a d f a e f AB FD AF AC FE AF)
  euclid_finish

theorem proposition_9' : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, (f.sameSide c AB) ∧ (f.sameSide b AC) ∧ (∠ b:a:f = ∠ c:a:f) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB a b (a─c)) as d
  euclid_apply (proposition_3 a c a d AC AB) as e
  euclid_apply (line_from_points d e) as DE
  euclid_apply (proposition_1' d e a DE) as f
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points a f) as AF
  use f
  have : ¬(f.onLine AB) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f d e AB DE FE)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  have : ¬(f.onLine AC) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f e d AC DE FD)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  euclid_apply (proposition_8 a d f a e f AB FD AF AC FE AF)
  euclid_apply (intersection_lines AF DE) as g
  euclid_finish

theorem proposition_10 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ d : Point, (between a d b) ∧ (|(a─d)| = |(d─b)|) :=
by
  euclid_intros
  euclid_apply (proposition_1 a b AB) as c
  euclid_apply (line_from_points c a) as AC
  euclid_apply (line_from_points c b ) as BC
  euclid_apply (proposition_9' c a b AC BC) as d'
  euclid_apply (line_from_points c d') as CD
  euclid_apply (intersection_lines CD AB) as d
  euclid_apply (proposition_4 c a d c b d AC AB CD BC AB CD)
  use d
  euclid_finish

theorem proposition_11 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB c a (c─b)) as d
  euclid_apply (proposition_3 c b c d AB AB) as e
  euclid_apply (proposition_1 d e AB) as f
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC)
  euclid_apply (perpendicular_if d e c f AB)
  use f
  euclid_finish

theorem proposition_11' : ∀ (a b c x : Point) (AB : Line),
  (distinctPointsOnLine a b AB) ∧ (between a c b) ∧ ¬(x.onLine AB) →
  exists f : Point, (f.sameSide x AB) ∧ (∠ a:c:f = ∟) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB c a (c─b)) as d
  euclid_apply (proposition_3 c b c d AB AB) as e
  euclid_apply (exists_point_opposite AB x) as h
  euclid_apply (proposition_1' d e h AB) as f
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC)
  euclid_apply (perpendicular_if d e c f AB)
  use f
  euclid_finish

theorem proposition_11'' : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  exists (f : Point), ¬(f.onLine AB) ∧ (∠ f:a:b = ∟) :=
by
  euclid_intros
  euclid_apply (extend_point AB b a) as c
  euclid_apply (proposition_11 c b a AB) as f
  use f
  euclid_finish

theorem proposition_11''' : ∀ (a b x : Point) (AB : Line),
  ¬(x.onLine AB) ∧ (distinctPointsOnLine a b AB) →
  exists (f : Point), ¬(f.onLine AB) ∧ (f.opposingSides x AB) ∧ (∠ f:a:b = ∟) :=
by
  euclid_intros
  euclid_apply (extend_point AB b a) as c
  euclid_apply (exists_point_opposite AB x) as g
  euclid_apply (proposition_11' c b a g AB) as f
  use f
  euclid_finish

theorem proposition_12 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  exists h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) :=
by
  euclid_intros
  euclid_apply (exists_point_opposite AB c) as d
  euclid_apply (circle_from_points c d) as EFG
  euclid_apply (intersections_circle_line EFG AB) as (e, g)
  euclid_apply (proposition_10 e g AB) as h
  euclid_apply (line_from_points c g) as CG
  euclid_apply (line_from_points c h) as CH
  euclid_apply (line_from_points c e) as CE
  use h
  euclid_apply (proposition_8 h c g h c e CH CG AB CH CE AB)
  euclid_finish

theorem proposition_13 : ∀ (a b c d : Point) (AB CD : Line),
  AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c →
  ∠ c:b:a + ∠ a:b:d = ∟ + ∟ :=
by
  euclid_intros
  by_cases ∠ c:b:a = ∠ a:b:d
  . euclid_finish
  . euclid_apply (proposition_11' d c b a CD) as e
    euclid_apply (line_from_points b e) as BE
    euclid_finish

theorem proposition_14 : ∀ (a b c d : Point) (AB BC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ (c.opposingSides d AB) ∧
  (∠ a:b:c + ∠ a:b:d) = ∟ + ∟ →
  BC = BD :=
by
  euclid_intros
  by_contra
  euclid_apply (extend_point BC c b) as e
  euclid_apply (proposition_13 a b e c AB BC)
  by_cases a.sameSide e BD
  . euclid_apply (sum_angles_onlyif b a d e AB BD)
    euclid_finish
  . -- Omitted by Euclid.
    euclid_apply (sum_angles_onlyif b a e d AB BC)
    euclid_finish

theorem proposition_15 : ∀ (a b c d e : Point) (AB CD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧
  CD ≠ AB ∧ (between d e c) ∧ (between a e b) →
  (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d) :=
by
   euclid_intros
   euclid_apply (proposition_13 a e c d AB CD)
   euclid_apply (proposition_13 d e a b CD AB)
   euclid_apply (proposition_13 c e a b CD AB)
   euclid_finish

theorem proposition_16 : ∀ (a b c d : Point) (AB BC AC: Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  (∠ a:c:d > ∠ c:b:a) ∧ (∠ a:c:d > ∠ b:a:c) :=
by
  euclid_intros
  constructor
  · -- Omitted by Euclid.
    euclid_apply (proposition_10 b c BC) as e
    euclid_apply (line_from_points a e) as AE
    euclid_apply (extend_point_longer AE a e (a─e)) as f'
    euclid_apply (proposition_3 e f' a e AE AE) as f
    euclid_apply (line_from_points f c) as FC
    euclid_apply (proposition_15 b c a f e BC AE)
    euclid_apply (proposition_4 e b a e c f BC AB AE BC FC AE)
    euclid_apply (extend_point AC a c) as g
    euclid_apply (proposition_15 a g b d c AC BC)
    euclid_finish
  · euclid_apply (proposition_10 a c AC) as e
    euclid_apply (line_from_points b e) as BE
    euclid_apply (extend_point_longer BE b e (b─e)) as f'
    euclid_apply (proposition_3 e f' b e BE BE) as f
    euclid_apply (line_from_points f c) as FC
    euclid_apply (proposition_15 a c b f e AC BE)
    euclid_apply (proposition_4 e b a e f c BE AB AC BE FC AC)
    euclid_finish

theorem proposition_17 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  ∠ a:b:c + ∠ b:c:a < ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (extend_point BC b c) as d
  euclid_apply (proposition_16 a b c d AB BC AC)
  euclid_apply (proposition_13 a c b d AC BC)
  euclid_finish

theorem proposition_18 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─c)| > |(a─b)|) →
  (∠ a:b:c > ∠ b:c:a) :=
by
  euclid_intros
  euclid_apply (proposition_3 a c a b AC AB) as d
  euclid_apply (line_from_points b d) as BD
  euclid_apply (proposition_16 b c d a BC AC BD)
  euclid_apply (proposition_5' a b d AB BD AC)
  euclid_apply (sum_angles_if b a c d AB BC)
  euclid_finish

theorem proposition_19 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c > ∠ b:c:a) →
  (|(a─c)| > |(a─b)|) :=
by
  euclid_intros
  by_contra
  by_cases |(a─c)| = |(a─b)|
  . euclid_apply (proposition_5' a b c AB BC AC)
    euclid_finish
  . euclid_apply (proposition_18 a c b AC BC AB)
    euclid_finish

theorem proposition_20 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC → |(b─a)| + |(a─c)| > |(b─c)| :=
by
  euclid_intros
  euclid_apply (extend_point_longer AB b a (c─a)) as d'
  euclid_apply (proposition_3 a d' a c AB AC) as d
  euclid_apply (line_from_points d c) as DC
  euclid_apply (proposition_5' a c d AC DC AB)
  euclid_apply (sum_angles_onlyif c b d a BC DC)
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

theorem proposition_21 : ∀ (a b c d : Point) (AB BC AC BD DC : Line),
  formTriangle a b c AB BC AC ∧ (a.sameSide d BC) ∧ (c.sameSide d AB) ∧ (b.sameSide d AC) ∧
  distinctPointsOnLine b d BD ∧ distinctPointsOnLine d c DC →
  (|(b─d)| + |(d─c)| < |(b─a)| + |(a─c)|) ∧ (∠ b:d:c > ∠ b:a:c) :=
by
  euclid_intros
  euclid_apply (intersection_lines BD AC) as e
  euclid_apply (proposition_20 a b e AB BD AC)
  euclid_apply (proposition_20 e d c BD DC AC)
  constructor
  . euclid_finish
  . euclid_apply (proposition_16 c e d b AC BD DC)
    euclid_apply (proposition_16 b a e c AB AC BD)
    euclid_finish

theorem proposition_22 : ∀ (a a' b b' c c' : Point) (A B C : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k f g : Point), (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply arbitrary_point as d
  euclid_apply (distinct_points d) as e'
  euclid_apply (line_from_points d e') as DE
  euclid_apply (extend_point_longer DE d e' (a─a')) as e''
  euclid_apply (extend_point_longer DE d e'' (b─b')) as e'''
  euclid_apply (extend_point_longer DE d e''' (c─c')) as e
  euclid_apply (proposition_3 d e a a' DE A ) as f
  euclid_apply (proposition_3 f e b b' DE B) as g
  euclid_apply (proposition_3 g e c c' DE C) as h
  euclid_apply (circle_from_points f d) as DKL
  euclid_apply (circle_from_points g h) as KLH
  -- Euclid didn't need to explicitly note the existence of i.
  euclid_apply (intersection_circle_line_extending_points KLH DE g h) as i
  euclid_apply (intersection_circles KLH DKL) as k
  use k, f, g
  euclid_apply (point_on_circle_onlyif f d k DKL)
  euclid_apply (point_on_circle_onlyif g k h KLH)
  euclid_finish

-- An extension of proposition 22 given a line and two points on it.
theorem proposition_22' : ∀ (a a' b b' c c' f e : Point) (A B C FE : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ distinctPointsOnLine f e FE ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k g : Point), g.onLine FE ∧ ¬(between g f e) ∧
  (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply (extend_point_longer FE f e (b─b')) as e'
  euclid_apply (extend_point_longer FE f e' (c─c')) as e''
  euclid_apply (proposition_3 f e'' a a' FE A) as d
  euclid_apply (proposition_3 f e'' b b' FE B) as g
  euclid_apply (proposition_3 g e'' c c' FE C) as h
  euclid_apply (circle_from_points f d) as DKL
  euclid_apply (circle_from_points g h) as KLH
  -- Euclid didn't need to explicitly note the existence of i.
  euclid_apply (intersection_circle_line_extending_points KLH FE g h) as i
  euclid_apply (intersection_circles KLH DKL) as k
  use k, g
  euclid_apply (point_on_circle_onlyif f d k DKL)
  euclid_apply (point_on_circle_onlyif g k h KLH)
  euclid_finish

theorem proposition_22'' : ∀ (a a' b b' c c' f e x : Point) (A B C FE : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ distinctPointsOnLine f e FE ∧ ¬(x.onLine FE) ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k g : Point), g.onLine FE ∧ ¬(between g f e) ∧ (k.sameSide x FE) ∧
  (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply (extend_point_longer FE f e (b─b')) as e'
  euclid_apply (extend_point_longer FE f e' (c─c')) as e''
  euclid_apply (proposition_3 f e'' a a' FE A) as d
  euclid_apply (proposition_3 f e'' b b' FE B) as g
  euclid_apply (proposition_3 g e'' c c' FE C) as h
  euclid_apply (circle_from_points f d) as DKL
  euclid_apply (circle_from_points g h) as KLH
  -- Euclid didn't need to explicitly note the existence of i.
  euclid_apply (intersection_circle_line_extending_points KLH FE g h) as i
  euclid_apply (intersection_same_side KLH DKL x g f FE) as k
  use k, g
  euclid_apply (point_on_circle_onlyif f d k DKL)
  euclid_apply (point_on_circle_onlyif g k h KLH)
  euclid_finish

theorem proposition_23 : ∀ (a b c d e : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE →
  ∃ f : Point, f ≠ a ∧ (∠ f:a:b = ∠ d:c:e) :=
by
  euclid_intros
  by_cases (d.onLine CE)
  · -- Omitted by Euclid.
    by_cases (∠ d:c:e = 0)
    · use b
      euclid_finish
    · euclid_assert ∠ d:c:e = ∟ + ∟
      euclid_apply (extend_point AB b a) as b'
      use b'
      euclid_finish
  euclid_apply (line_from_points d e) as DE
  -- Euclid didn't explicitly apply proposition_20.
  euclid_apply (proposition_20 c d e CD DE CE)
  euclid_apply (proposition_20 d e c DE CE CD)
  euclid_apply (proposition_20 e c d CE CD DE)
  euclid_apply (proposition_22' c d c e e d a b CD CE DE AB) as (f, g)
  euclid_apply (line_from_points a f) as FA
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_8 c d e a f g CD DE CE FA FG AB)
  use f
  euclid_finish

-- An extension of proposition_23 that allows the angle to be constructed on either side of AB.
theorem proposition_23' : ∀ (a b c d e x : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE ∧ ¬(x.onLine AB) →
  ∃ f : Point, f ≠ a ∧ (f.onLine AB ∨ f.sameSide x AB) ∧ (∠ f:a:b = ∠ d:c:e) :=
by
  euclid_intros
  by_cases (d.onLine CE)
  . -- Omitted by Euclid.
    by_cases (∠ d:c:e = 0)
    . use b
      euclid_finish
    . euclid_assert ∠ d:c:e = ∟ + ∟
      euclid_apply (extend_point AB b a) as b'
      use b'
      euclid_finish
  euclid_apply (line_from_points d e) as DE
  -- Euclid didn't explicitly apply proposition_20.
  euclid_apply (proposition_20 c d e CD DE CE)
  euclid_apply (proposition_20 d e c DE CE CD)
  euclid_apply (proposition_20 e c d CE CD DE)
  euclid_apply (proposition_22'' c d c e e d a b x CD CE DE AB) as (f, g)
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_8 c d e a f g CD DE CE AF FG AB)
  use f
  euclid_finish

theorem proposition_24 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c > ∠ e:d:f) →
  |(b─c)| > |(e─f)| :=
by
  euclid_intros
  euclid_apply (proposition_23' d e a b c f DE AB AC) as g'
  euclid_apply (line_from_points d g') as DG
  euclid_apply (extend_point_longer DG d g' (a─c)) as g''
  euclid_apply (proposition_3 d g'' a c DG AC) as g
  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_4 a b c d e g AB BC AC DE EG DG)
  euclid_apply (proposition_5' d g f DG FG DF)
  by_cases (d.sameSide g EF)
  · euclid_assert (∠ d:f:g > ∠ e:g:f)
    euclid_assert (∠ e:f:g > ∠ e:g:f)
    euclid_apply (proposition_19 e f g EF FG EG)
    euclid_finish
  · -- Omitted by Euclid.
    by_cases g.onLine EF
    · euclid_finish
    · euclid_apply (extend_point FG g f) as h
      -- Not clear why these are needed.
      euclid_assert ¬(g.onLine DF)
      euclid_assert ¬(e.onLine DF)
      euclid_assert (g.opposingSides e DF)
      euclid_assert h.sameSide e DF

      euclid_apply (proposition_13 d f g h DF FG)
      euclid_apply (proposition_13 e f g h EF FG)
      euclid_apply (proposition_17 d g e DG EG DE)
      euclid_apply (proposition_17 d f e DF EF DE)
      euclid_assert (∠ d:g:e < ∟ + ∟)
      euclid_assert (∠ d:f:e < ∟ + ∟)
      euclid_assert (∠ e:f:g + ∠ g:f:d + ∠ d:f:e = ∟ + ∟ + ∟ + ∟)
      euclid_assert (∠ e:f:g > ∠ e:g:f)
      euclid_apply (proposition_19 e f g EF FG EG)
      euclid_finish

theorem proposition_25 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (|(b─c)| > |(e─f)|) →
  (∠ b:a:c > ∠ e:d:f) :=
by
  euclid_intros
  by_contra
  by_cases (∠ b:a:c = ∠ e:d:f)
  · euclid_apply (proposition_4 a b c d e f AB BC AC DE EF DF)
    euclid_finish
  · euclid_assert (∠ b:a:c < ∠ e:d:f)
    euclid_apply (proposition_24 d e f a b c DE EF DF AB BC AC)
    euclid_finish

theorem proposition_26 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (∠ a:b:c = ∠ d:e:f) ∧ (∠ b:c:a = ∠ e:f:d) ∧ (|(b─c)| = |(e─f)| ∨ |(a─b)| = |(d─e)|) →
  (|(a─b)| = |(d─e)|) ∧ (|(b─c)| = |(e─f)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c = ∠ e:d:f) :=
by
  euclid_intros
  split_ors
  · have : (|(a─b)| = |(d─e)|) := by
      by_contra
      by_cases (|(a─b)| > |(d─e)|)
      · euclid_apply (proposition_3 b a e d AB DE) as g
        euclid_apply (line_from_points g c) as GC
        euclid_apply (proposition_4 b g c e d f AB GC BC DE DF EF)
        euclid_finish
      · -- Omitted by Euclid.
        euclid_assert (|(d─e)| > |(a─b)|)
        euclid_apply (proposition_3 e d b a DE AB) as g
        euclid_apply (line_from_points g f) as GF
        euclid_apply (proposition_4 e g f b a c DE GF EF AB AC BC)
        euclid_finish
    euclid_apply (proposition_4 b a c e d f AB AC BC DE DF EF)
    euclid_finish
  · have : (|(b─c)| = |(e─f)|) := by
      by_contra
      by_cases (|(b─c)| > |(e─f)|)
      · euclid_apply (proposition_3 b c e f BC EF) as h
        euclid_apply (line_from_points a h)  as AH
        euclid_apply (proposition_4 b a h e d f AB AH BC DE DF EF)
        euclid_apply (proposition_16 a c h b AC BC AH)
        euclid_finish
      · -- Omitted by Euclid.
        euclid_assert (|(e─f)| > |(b─c)|)
        euclid_apply (proposition_3 e f b c EF BC) as h
        euclid_apply (line_from_points d h) as DH
        euclid_apply (proposition_4 e d h b a c DE DH EF AB AC BC)
        euclid_apply (proposition_16 d f h e DF EF DH)
        euclid_finish
    euclid_apply (proposition_4 b a c e d f AB AC BC DE DF EF)
    euclid_finish

theorem proposition_27 : ∀ (a d e f : Point) (AE FD EF : Line),
  distinctPointsOnLine a e AE ∧ distinctPointsOnLine f d FD ∧ distinctPointsOnLine e f EF ∧
  a.opposingSides d EF ∧ (∠ a:e:f = ∠ e:f:d) →
  ¬(AE.intersectsLine FD) :=
by
  euclid_intros
  by_contra
  euclid_apply (extend_point AE a e) as b
  euclid_apply (intersection_lines AE FD) as g
  by_cases (g.sameSide b EF)
  . euclid_apply (proposition_16 f g e a FD AE EF)
    euclid_finish
  . -- Omitted by Euclid.
    euclid_apply (proposition_16 e g f d AE FD EF)
    euclid_finish

theorem proposition_28 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧
  (∠ e:g:b = ∠ g:h:d ∨ ∠ b:g:h + ∠ g:h:d = ∟ + ∟) →
  ¬(AB.intersectsLine CD) :=
by
  euclid_intros
  split_ors
  . euclid_apply (proposition_15 a b e h g AB EF)
    euclid_apply (proposition_27 a d g h AB CD EF)
    euclid_finish
  . euclid_apply (proposition_13 h g a b EF AB)
    euclid_apply (proposition_27 a d g h AB CD EF)
    euclid_finish

theorem proposition_29 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD)
  → ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
  euclid_intros
  have : ∠ a:g:h = ∠ g:h:d := by
    by_contra
    by_cases ∠ a:g:h > ∠ g:h:d
    · euclid_assert ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d
      euclid_apply (proposition_13 h g a b EF AB)
      euclid_assert ∠ b:g:h + ∠ g:h:d < ∟ + ∟
      euclid_finish
    · -- Omitted by Euclid.
      euclid_assert ∠ a:g:h < ∠ g:h:d
      euclid_assert ∠ a:g:h + ∠ c:h:g < ∠ g:h:d + ∠ c:h:g
      euclid_apply (proposition_13 g h c d EF CD)
      euclid_assert ∠ a:g:h + ∠ c:h:g < ∟ + ∟
      euclid_finish

  euclid_apply (proposition_15 a b e h g AB EF)
  euclid_apply (proposition_13 b g e h AB EF)
  euclid_finish

theorem proposition_29' : ∀ (a b c d e g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine g h EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
    euclid_intros
    euclid_apply (extend_point EF g h) as f
    euclid_apply (proposition_29 a b c d e f g h AB CD EF)
    euclid_finish

theorem proposition_29'' : ∀ (a b d g h : Point) (AB CD GH : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h GH ∧
  (between a g b) ∧ (b.sameSide d GH) ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
    euclid_intros
    euclid_apply (extend_point GH g h) as f
    euclid_apply (extend_point GH h g) as e
    euclid_apply (extend_point CD d h) as c
    euclid_apply (proposition_29 a b c d e f g h AB CD GH)
    euclid_finish

theorem proposition_29''' : ∀ (a d g h : Point) (AB CD GH : Line),
  distinctPointsOnLine a g AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h GH ∧
  a.opposingSides d GH ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d :=
by
  euclid_intros
  euclid_apply (extend_point AB a g) as b
  euclid_apply (proposition_29'' a b d g h AB CD GH)
  euclid_finish

theorem proposition_29'''' : ∀ (b d e g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine e h EF ∧
  between e g h ∧ b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ e:g:b = ∠ g:h:d :=
by
  euclid_intros
  euclid_apply (extend_point AB b g) as a
  euclid_apply (extend_point CD d h) as c
  euclid_apply (extend_point EF g h) as f
  euclid_apply (proposition_29 a b c d e f g h AB CD EF)
  euclid_finish

theorem proposition_29''''' : ∀ (b d g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h EF ∧
  b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (extend_point AB b g) as a
  euclid_apply (extend_point CD d h) as c
  euclid_apply (extend_point EF g h) as f
  euclid_apply (extend_point EF h g) as e
  euclid_apply (proposition_29 a b c d e f g h AB CD EF)
  euclid_finish

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

theorem proposition_32 : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  ∠ a:c:d = ∠ c:a:b + ∠ a:b:c ∧
  ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ :=
by
  euclid_intros

  have : (∠ a:c:d : ℝ) = (∠ c:a:b) + (∠ a:b:c) := by
    euclid_apply (proposition_31 c a b AB ) as CE
    euclid_apply (point_on_line_same_side BC CE a ) as e
    euclid_apply (proposition_29''' b e a c AB CE AC)
    euclid_apply (proposition_29'''' e a d c b CE AB BC)
    euclid_finish

  constructor
  · assumption
  · euclid_apply (proposition_13 a c b d AC BC)
    euclid_finish

theorem proposition_33 : ∀ (a b c d : Point) (AB CD AC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  (a.sameSide c BD) ∧ ¬(AB.intersectsLine CD) ∧ |(a─b)| = |(c─d)| →
  AC ≠ BD ∧ ¬(AC.intersectsLine BD) ∧ |(a─c)|= |(b─d)| :=
by
  euclid_intros
  euclid_apply (line_from_points b c ) as BC
  euclid_apply (proposition_29''' a d b c AB CD BC)
  euclid_apply (proposition_4 c b d b c a BC BD CD BC AC AB)
  euclid_apply (proposition_27 a d c b AC BD BC)
  euclid_finish

theorem proposition_34 : ∀ (a b c d : Point) (AB CD AC BD BC : Line),
  formParallelogram a b c d AB CD AC BD ∧ distinctPointsOnLine b c BC →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c  = ∠ c:d:b ∧
  Triangle.area △ a:b:c = Triangle.area △ d:c:b :=
by
  euclid_intros
  euclid_apply (proposition_29''' a d b c AB CD BC)
  euclid_apply (proposition_29''' a d c b AC BD BC)
  euclid_apply (proposition_26 a b c d c b AB BC AC CD BC BD)
  euclid_finish

theorem proposition_34' : ∀ (a b c d : Point) (AB CD AC BD : Line),
  formParallelogram a b c d AB CD AC BD →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b :=
by
  euclid_intros
  euclid_apply (line_from_points b c) as BC
  euclid_apply (proposition_34 a b c d AB CD AC BD BC)
  euclid_finish

theorem proposition_35 : ∀ (a b c d e f g : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC ∧
  between a d e ∧ between d e f ∧ g.onLine CD ∧ g.onLine EB →
  Triangle.area △a:b:d + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f :=
by
  euclid_intros
  euclid_apply (proposition_34' a d b c AF BC AB CD)
  euclid_apply (proposition_34' e f b c AF BC EB FC)
  euclid_assert (|(a─d)| = |(e─f)|)
  euclid_assert (|(a─e)| = |(d─f)|)
  euclid_apply (proposition_29'''' c b f d a CD AB AF)
  euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD)
  euclid_finish

theorem proposition_35' : ∀ (a b c d e f : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC →
  Triangle.area △a:b:d  + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f :=
by
  euclid_intros
  euclid_apply (proposition_34' a d b c AF BC AB CD)
  euclid_apply (proposition_34' e f b c AF BC EB FC)
  euclid_assert (|(a─d)| = |(e─f)|)
  by_cases (between a d f)
  · euclid_apply (intersection_lines CD EB) as g
    by_cases (between a d e)
    · euclid_apply (proposition_35 a b c d e f g AF BC AB CD EB FC)
      euclid_finish
    · euclid_apply (proposition_29'''' c b f d a CD AB AF)
      euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD)
      euclid_finish
  · by_cases (a = e)
    · euclid_finish
    · euclid_apply (intersection_lines FC AB) as g
      by_cases (between e f a)
      · euclid_apply (proposition_35 e b c f a d g AF BC EB FC AB CD)
        euclid_finish
      · euclid_apply (proposition_29'''' c b d f e FC EB AF)
        euclid_apply (proposition_4 e a b f d c AF AB EB AF CD FC)
        by_cases (f = a)
        · euclid_finish
        · euclid_assert (Triangle.area △ e:a:b + Triangle.area △ g:b:c = Triangle.area △ f:d:c + Triangle.area △ g:b:c)
          euclid_finish

theorem proposition_36 : ∀ (a b c d e f g h : Point) (AH BG AB CD EF HG : Line),
  formParallelogram a d b c AH BG AB CD ∧ formParallelogram e h f g AH BG EF HG ∧
  |(b─c)| = |(f─g)| ∧ (between a d h) ∧ (between a e h) →
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g :=
by
  euclid_intros
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c h) as CH
  euclid_apply (proposition_34' e h f g AH BG EF HG)
  euclid_assert (|(b─c)| = |(e─h)|)
  euclid_apply (proposition_33 e h b c AH BG BE CH)
  euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
  euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
  euclid_finish

theorem proposition_36' : ∀ (a b c d e f g h : Point) (AH BG AB CD EF HG : Line) ,
  formParallelogram a d b c AH BG AB CD ∧ formParallelogram e h f g AH BG EF HG ∧
  |(b─c)| = |(f─g)| →
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g :=
by
  euclid_intros
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c h) as CH
  by_cases (e.sameSide b CH)
  . euclid_apply (line_from_points h f) as HF
    euclid_apply (proposition_34 e h f g AH BG EF HG HF)
    euclid_assert (|(b─c)| = |(e─h)|)
    euclid_apply (proposition_33 e h b c AH BG BE CH)
    euclid_assert (formParallelogram e h b c AH BG BE CH)
    euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
    euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
    euclid_finish
  . euclid_apply (line_from_points b h) as BH
    euclid_apply (line_from_points c e) as CE
    euclid_apply (line_from_points e g) as EG
    euclid_apply (proposition_34 h e g f AH BG HG EF EG)
    euclid_assert (|(b─c)| = |(e─h)|)
    euclid_apply (proposition_33 h e b c AH BG BH CE)
    euclid_assert (formParallelogram h e b c AH BG BH CE)
    euclid_apply (proposition_35' a b c d h e AH BG AB CD BH CE)
    euclid_apply (proposition_35' f e h g c b BG AH EF HG CE BH)
    euclid_finish

theorem proposition_37 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) ∧ d.sameSide c AB →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
by
  euclid_intros
  euclid_apply (proposition_31 b a c AC) as BE
  euclid_apply (intersection_lines AD BE) as e
  euclid_apply (proposition_31 c b d BD) as CF
  euclid_apply (intersection_lines AD CF) as f
  euclid_apply (proposition_35' e b c a d f AD BC BE AC BD CF)
  euclid_apply (proposition_34 e a b c AD BC BE AC AB)
  euclid_apply (proposition_34 f d c b AD BC CF BD CD)
  euclid_finish

theorem proposition_37' : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
by
  euclid_intros
  by_cases (d.sameSide c AB)
  . euclid_apply (proposition_37 a b c d AB BC AC BD CD AD)
    assumption
  . euclid_apply (proposition_37 d b c a BD BC CD AB AC AD)
    euclid_finish

theorem proposition_38 : ∀ (a b c d e f: Point) (AD BF AB AC DE DF : Line),
  a.onLine AD ∧ d.onLine AD ∧ formTriangle a b c AB BF AC ∧ formTriangle d e f DE BF DF ∧
  ¬(AD.intersectsLine BF) ∧ (between b c f) ∧ (between b e f) ∧ |(b─c)| = |(e─f)| →
  Triangle.area △ a:b:c = Triangle.area △ d:e:f :=
by
  euclid_intros
  euclid_apply (proposition_31 b a c AC) as BG
  euclid_apply (intersection_lines AD BG) as g
  euclid_apply (proposition_31 f d e DE) as FH
  euclid_apply (intersection_lines AD FH) as h
  euclid_apply (proposition_36' g b c a d e f h AD BF BG AC DE FH)
  euclid_apply (proposition_34 g a b c AD BF BG AC AB)
  euclid_apply (proposition_34 e f d h BF AD DE FH DF)
  euclid_finish

theorem proposition_39 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ a.sameSide d BC ∧
  (△ a:b:c : ℝ) = (△ d:b:c) ∧ distinctPointsOnLine a d AD →
  ¬(AD.intersectsLine BC) :=
by
  euclid_intros
  by_contra
  by_cases c.sameSide d AB
  . euclid_apply (proposition_31 a b c BC) as AE
    euclid_apply (intersection_lines AE BD) as e
    euclid_apply (line_from_points e c) as EC
    euclid_apply (proposition_37 a b c e AB BC AC BD EC AE)
    euclid_assert (△ e:b:c : ℝ) = (△ d:b:c)
    euclid_finish
  . -- Omitted by Euclid.
    euclid_assert a.sameSide c BD
    euclid_apply (proposition_31 d b c BC) as DE
    euclid_apply (intersection_lines DE AB) as e
    euclid_apply (line_from_points e c) as EC
    euclid_apply (proposition_37 d b c e BD BC CD AB EC DE)
    euclid_assert (△ e:b:c : ℝ) = (△ a:b:c)

    -- Not sure why this is necessary.
    by_cases (between a e b)
    · euclid_apply (sum_areas_if a b e c AB)
      euclid_assert e = a
      euclid_finish
    · euclid_assert (between e a b)
      euclid_apply (sum_areas_if e b a c AB)
      euclid_assert e = a
      euclid_finish

theorem proposition_40 : ∀  (a b c d e : Point) (AB BC AC CD DE AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d c e CD BC DE ∧ a.sameSide d BC ∧ b ≠ e ∧ |(b─c)| = |(c─e)| ∧
  distinctPointsOnLine a d AD ∧ (Triangle.area △ a:b:c = Triangle.area △ d:c:e) →
  ¬(AD.intersectsLine BC) :=
by
  euclid_intros
  by_contra
  euclid_apply (proposition_31 a b c BC) as AF
  euclid_apply (intersection_lines AF CD) as f
  by_cases (a = f)
  . -- Omitted by Euclid.
    euclid_apply (intersection_lines AF DE) as g
    euclid_apply (line_from_points g c) as GC
    euclid_apply (proposition_38 a b c g c e AF BC AB AC GC DE)
    euclid_assert (Triangle.area △ d:c:e : ℝ) = (Triangle.area △ g:c:e)
    euclid_finish
  . euclid_apply (line_from_points f e) as FE
    euclid_apply (proposition_38 a b c f c e AF BC AB AC CD FE)
    euclid_assert ((Triangle.area △ d:c:e : ℝ) = Triangle.area △ f:c:e)
    euclid_finish

theorem proposition_41 : ∀ (a b c d e : Point) (AE BC AB CD BE CE : Line),
  formParallelogram a d b c AE BC AB CD ∧ formTriangle e b c BE BC CE ∧ e.onLine AE ∧ ¬(AE.intersectsLine  BC) →
  (Triangle.area △ a:b:c : ℝ) + (Triangle.area △ a:c:d) = (Triangle.area △ e:b:c) + (Triangle.area △ e :b :c) :=
by
  euclid_intros
  euclid_apply (line_from_points a c) as AC
  by_cases (a = e)
  . -- Omitted by Euclid.
    euclid_assert (Triangle.area △ a:b:c : ℝ) = (Triangle.area △ e:b:c)
    euclid_apply (proposition_34 d a c b AE BC CD AB AC)
    euclid_finish
  . euclid_apply (proposition_37' a b c e AB BC AC BE CE AE)
    euclid_apply (proposition_34 d a c b AE BC CD AB AC)
    euclid_finish

theorem proposition_42 : ∀ (a b c d₁ d₂ d₃ : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g e c' : Point) (FG EC EF CG : Line), formParallelogram f g e c' FG EC EF CG ∧
  (∠ c':e:f = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c' + Triangle.area △ f:c':g = Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_10 b c BC) as e
  euclid_apply (line_from_points a e) as AE
  euclid_apply (proposition_23' e c d₂ d₁ d₃ a BC D₁₂ D₂₃) as f'
  euclid_apply (line_from_points e f') as EF
  euclid_apply (proposition_31 a b c BC) as AG
  euclid_apply (intersection_lines AG EF) as f
  euclid_apply (proposition_31 c e f EF) as CG
  euclid_apply (intersection_lines CG AG) as g
  euclid_assert (formParallelogram f g e c AG BC EF CG)
  euclid_apply (proposition_38 a b e a e c AG BC AB AE AE AC)
  euclid_apply (proposition_41 f e c g a AG BC EF CG AE AC)
  use f, g, e, c, AG, BC, EF, CG
  euclid_finish

theorem proposition_42' : ∀ (a b c d₁ d₂ d₃ e : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ between b e c ∧ (|(b─e)| = |(e─c)|) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g : Point) (FG EF CG : Line), a.sameSide f BC ∧ formParallelogram f g e c FG BC EF CG ∧
  (∠ c:e:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c : ℝ) + (Triangle.area △ f:c:g) = (Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (line_from_points a e) as AE
  euclid_apply (proposition_23' e c d₂ d₁ d₃ a BC D₁₂ D₂₃) as fn
  euclid_apply (line_from_points e fn) as EF
  euclid_apply (proposition_31 a b c BC) as AG
  euclid_apply (intersection_lines AG EF) as f
  euclid_apply (proposition_31 c e f EF) as CG
  euclid_apply (intersection_lines CG AG) as g
  euclid_assert (formParallelogram f g e c AG BC EF CG)
  euclid_apply (proposition_38 a b e a e c AG BC AB AE AE AC)
  euclid_apply (proposition_41 f e c g a AG BC EF CG AE AC)
  use f, g, AG, EF, CG
  euclid_finish

theorem proposition_42'' : ∀ (a b c d₁ d₂ d₃ h i : Point) (AB BC AC D₁₂ D₂₃ HI : Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ ∧ distinctPointsOnLine h i HI →
  ∃ (f g j : Point) (FG FI GJ : Line), between h i j ∧ formParallelogram f g i j FG HI FI GJ ∧
  (∠ j:i:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:i:j : ℝ) + (Triangle.area △ f:j:g) = (Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_10 b c BC) as e
  euclid_apply (extend_point_longer HI h i (e─c)) as i''
  euclid_apply (proposition_3 i i'' e c HI BC) as j
  euclid_apply (extend_point_longer HI i h (e─c)) as h'
  euclid_apply (proposition_3 i h' e c HI BC) as k
  euclid_apply (proposition_23 k j b a c HI AB BC) as l'
  euclid_apply (line_from_points k l') as KL
  euclid_apply (extend_point_longer KL k l' (a─b)) as l''
  euclid_apply (proposition_3 k l'' b a KL AB) as l
  euclid_apply (line_from_points l j) as LJ
  euclid_apply (proposition_4 k j l b c a HI LJ KL BC AC AB)
  euclid_apply (proposition_42' l k j d₁ d₂ d₃ i KL HI LJ D₁₂ D₂₃) as (f, g, FG, FI, GJ)
  use f, g, j, FG, FI, GJ
  euclid_finish

theorem proposition_42''' : ∀ (a b c d₁ d₂ d₃ h i x : Point) (AB BC AC D₁₂ D₂₃ HI : Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ ¬(x.onLine HI) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ ∧ distinctPointsOnLine h i HI →
  ∃ (f g j : Point) (FG FI GJ : Line), f.sameSide x HI ∧ between h i j ∧ formParallelogram f g i j FG HI FI GJ ∧
  (∠ j:i:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:i:j : ℝ) + (Triangle.area △ f:j:g) = (Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_10 b c BC) as e
  euclid_apply (extend_point_longer HI h i (e─c)) as i''
  euclid_apply (proposition_3 i i'' e c HI BC) as j
  euclid_apply (extend_point_longer HI i h (e─c)) as h'
  euclid_apply (proposition_3 i h' e c HI BC) as k
  euclid_apply (proposition_23' k j b a c x HI AB BC) as l'
  euclid_apply (line_from_points k l') as KL
  euclid_apply (extend_point_longer KL k l' (a─b)) as l''
  euclid_apply (proposition_3 k l'' b a KL AB) as l
  euclid_apply (line_from_points l j) as LJ
  euclid_apply (proposition_4 k j l b c a HI LJ KL BC AC AB)
  euclid_apply (proposition_42' l k j d₁ d₂ d₃ i KL HI LJ D₁₂ D₂₃) as (f, g, FG, FI, GJ)
  use f, g, j, FG, FI, GJ
  euclid_finish

theorem proposition_43 : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  (Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) :=
by
  euclid_intros
  euclid_apply (proposition_34 d a c b AD BC CD AB AC)
  euclid_apply (proposition_34 h a k e AD EF GH AB AC)
  euclid_apply (proposition_34 f k c g EF BC CD GH AC)
  euclid_assert (Triangle.area △ a:e:k : ℝ) + (Triangle.area △ k:g:c) = (Triangle.area △ a:h:k) + (Triangle.area △ k:f:c)
  euclid_assert (Triangle.area △ a:h:k : ℝ) + (Triangle.area △ k:f:c) + (Triangle.area △ h:k:f) + (Triangle.area △ h:f:d) = (Triangle.area △ d:a:c)
  euclid_finish

theorem proposition_44 : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃) :=
by
  euclid_intros
  euclid_apply (proposition_42'' c₁ c₂ c₃ d₁ d₂ d₃ a b C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ AB) as (g, f, e, FG, BG, EF)
  euclid_apply (proposition_31 a b g BG) as AH
  euclid_apply (proposition_30 AH EF BG)
  euclid_apply (intersection_lines AH FG) as h
  euclid_apply (line_from_points h b) as HB
  euclid_apply (proposition_29''''' e a f h EF AH FG)
  euclid_apply (intersection_lines HB EF) as k
  euclid_apply (proposition_31 k e a AB) as KL
  euclid_apply (proposition_30 KL FG AB)
  euclid_apply (intersection_lines AH KL) as l
  euclid_apply (intersection_lines BG KL) as m
  euclid_apply (proposition_43 h f k l g m e a b AH EF FG KL HB BG AB)
  euclid_apply (proposition_15 e a m g b AB BG)
  use m, l, BG, AH, KL
  euclid_finish

theorem proposition_44' : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ x : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), Point.opposingSides m x AB ∧ formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m) + (Triangle.area △ a:l:m) = (Triangle.area △ c₁:c₂:c₃) :=
by
  euclid_intros
  euclid_apply (proposition_42''' c₁ c₂ c₃ d₁ d₂ d₃ a b x C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ AB) as (g, f ,e ,FG, BG, EF)
  euclid_apply (proposition_31 a b g BG) as AH
  euclid_apply (proposition_30 AH EF BG)
  euclid_apply (intersection_lines AH FG) as h
  euclid_apply (line_from_points h b) as HB
  euclid_apply (proposition_29''''' e a f h EF AH FG)
  euclid_apply (intersection_lines HB EF) as k
  euclid_apply (proposition_31 k e a AB) as KL
  euclid_apply (proposition_30 KL FG AB)
  euclid_apply (intersection_lines AH KL) as l
  euclid_apply (intersection_lines BG KL) as m
  euclid_apply (proposition_43 h f k l g m e a b AH EF FG KL HB BG AB)
  euclid_apply (proposition_15 e a m g b AB BG)
  use m, l, BG, AH, KL
  euclid_finish

theorem proposition_45 : ∀ (a b c d e₁ e₂ e₃ : Point) (AB BC CD AD DB E₁₂ E₂₃ : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB ∧
  formRectilinearAngle e₁ e₂ e₃ E₁₂ E₂₃ ∧ ∠ e₁:e₂:e₃ > 0 ∧ ∠ e₁:e₂:e₃ < ∟ + ∟ →
  ∃ (f l k m : Point) (FL KM FK LM : Line), formParallelogram f l k m FL KM FK LM ∧
  (∠ f:k:m = ∠ e₁:e₂:e₃) ∧ (Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_42 a b d e₁ e₂ e₃ AB DB AD E₁₂ E₂₃) as (f, g, k, h , FG, KH, FK, GH)
  euclid_apply (proposition_44' g h d b c e₁ e₂ e₃ k GH DB BC CD E₁₂ E₂₃) as (m, l, HM, G, LM)
  euclid_assert ((∠ h:k:f : ℝ) = ∠ g:h:m)
  euclid_assert ((∠ h:k:f : ℝ) + (∠ k:h:g) = (∠ g:h:m) + (∠ k:h:g))
  euclid_apply (proposition_29''''' f g k h FK GH KH)
  euclid_assert ((∠ k:h:g : ℝ) + (∠ g:h:m) = ∟ + ∟)
  euclid_apply (proposition_14 g h k m GH KH HM)
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_assert ((∠ m:h:g : ℝ) + (∠ h:g:l) = (∠ h:g:f) + (∠ h:g:l))
  euclid_apply (proposition_29''''' l m g h G HM GH)
  euclid_assert ((∠ h:g:f : ℝ) + (∠ h:g:l) = ∟ + ∟)
  euclid_apply (proposition_14 h g f l GH FG G)
  euclid_apply (proposition_34' f g k h FG KH FK GH)
  euclid_apply (proposition_34' h m g l HM G GH LM)
  euclid_assert (|(k─f)| = |(m─l)|)
  euclid_apply (proposition_30 FK LM GH)
  euclid_assert (|(f─l)| = |(k─m)|)
  euclid_apply (proposition_33 f l k m FG KH FK LM)
  use f, l, k, m, FG, KH, FK, LM
  euclid_finish

theorem proposition_46 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) :=
by
  euclid_intros
  euclid_apply (proposition_11'' a b AB) as c'
  euclid_apply (line_from_points a c') as AC
  euclid_apply (extend_point_longer AC a c' (a─b)) as c
  euclid_apply (proposition_3 a c a b AC AB) as d
  euclid_apply (proposition_31 d a b AB) as DE
  euclid_apply (proposition_31 b a d AC) as BE
  euclid_apply (intersection_lines DE BE) as e
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  euclid_apply (proposition_29''''' e b d a DE AB AC)
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  use d, e, DE, AC, BE
  euclid_finish

theorem proposition_46' : ∀ (a b x : Point) (AB : Line), ¬(x.onLine AB) ∧ distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), d.opposingSides x AB ∧ formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d : ℝ) = ∟ ∧ (∠ a:d:e : ℝ) = ∟ ∧ (∠ a:b:e : ℝ) = ∟ ∧ (∠ b:e:d : ℝ) = ∟ :=
by
  euclid_intros
  euclid_apply (proposition_11''' a b x AB) as c'
  euclid_apply (line_from_points a c') as AC
  euclid_apply (extend_point_longer AC a c' (a─b)) as c
  euclid_apply (proposition_3 a c a b AC AB) as d
  euclid_apply (proposition_31 d a b AB) as DE
  euclid_apply (proposition_31 b a d AC) as BE
  euclid_apply (intersection_lines DE BE) as e
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  euclid_apply (proposition_29''''' e b d a DE AB AC)
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  use d, e, DE, AC, BE
  euclid_finish

-- WARNING: This proof is quite slow.
set_option maxHeartbeats 0 in
theorem proposition_47 : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| :=
by
  euclid_intros
  euclid_apply (proposition_46' b a c AB) as (f, g, FG, BF, AG)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)

  -- Missed by Euclid.
  have : (∠ a:b:c : ℝ) < ∟ := by
    euclid_apply (proposition_17 c a b AC AB BC)
    euclid_finish

  -- Missed by Euclid.
  have : ¬(d.onLine AB) := by
    by_contra
    euclid_apply (proposition_13 c b a d BC AB)
    euclid_finish

  -- Missed by Euclid.
  have : (d.sameSide c AB) := by
    euclid_apply (extend_point AB a b) as b'
    euclid_apply (proposition_16 c a b b' AC AB BC)
    euclid_assert (∠ c:b:b' : ℝ) > ∟
    euclid_finish

  -- Missed by Euclid.
  have : (∠ a:c:b : ℝ) < ∟ := by
    euclid_apply (proposition_17 b c a BC AC AB)
    euclid_finish

  -- Missed by Euclid.
  have : ¬(e.onLine AC) := by
    by_contra
    euclid_apply (proposition_13 b c a e BC AC)
    euclid_finish

  -- Missed by Euclid.
  have : (e.sameSide b AC) := by
    euclid_apply (extend_point AC a c) as c'
    euclid_apply (proposition_16 b a c c' AB AC BC)
    euclid_assert (∠ b:c:c' : ℝ) > ∟
    euclid_finish

  euclid_apply (proposition_31 a b d BD) as AL
  euclid_apply (proposition_30 AL CE BD)
  euclid_apply (intersection_lines AL DE) as l
  euclid_apply (intersection_lines AL BC) as l'
  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_14 b a c g AB AC AG)
  euclid_apply (proposition_14 c a b h AC AB AH)
  euclid_assert ((∠ d:b:a : ℝ) = ∠ f:b:c)
  euclid_assert ((∠ c:b:a : ℝ) + ∟ = ∠ c:b:f)
  euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
  euclid_assert ((Triangle.area △ a:b:d) = Triangle.area △ b:c:f)
  euclid_apply (proposition_41 l' b d l a AL BD BC DE AB AD)
  euclid_apply (proposition_41 g f b a c AG BF FG AB FC BC)
  euclid_assert ((Triangle.area △ g:f:b : ℝ) + (Triangle.area △ g:b:a) = (Triangle.area △ l':b:d) + (Triangle.area △ l':d:l))
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b k) as BK
  euclid_apply sum_angles_onlyif c e a b CE AC
  euclid_apply sum_angles_onlyif c k b a CK BC
  euclid_assert ((∠ e:c:a : ℝ) = (∠ k:c:b))
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_assert ((Triangle.area △ a:c:e : ℝ) = Triangle.area △ c:b:k)
  euclid_apply (proposition_41 l' c e l a AL CE BC DE AC AE)
  euclid_apply (proposition_41 h k c a b AH CK HK AC BK BC)
  euclid_assert ((Triangle.area △ k:c:a : ℝ) + (Triangle.area △ k:a:h) = (Triangle.area △ l':c:e) + (Triangle.area △ l':e:l))
  euclid_apply (rectangle_area b c d e BC DE BD CE)
  euclid_apply (rectangle_area b a f g AB FG BF AG)
  euclid_apply (rectangle_area a c h k AC HK AH CK)
  euclid_apply sum_parallelograms_area b c d e l' l BC DE BD CE
  euclid_apply parallelogram_area b l' d l BC DE BD AL
  euclid_assert ((Triangle.area △ b:d:e : ℝ) + (Triangle.area △ b:e:c) = (Triangle.area △ g:f:b) + (Triangle.area △ g:b:a) + (Triangle.area △ k:c:a) + (Triangle.area △ k:a:h))
  euclid_finish

theorem proposition_48 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| →
  ∠ b:a:c = ∟ :=
by
  euclid_intros
  euclid_apply (proposition_11'' a c AC) as d'
  euclid_apply (line_from_points a d') as AD
  euclid_apply (extend_point AD d' a) as d''
  euclid_apply (extend_point_longer AD d'' a (a─b)) as d'''
  euclid_apply (proposition_3 a d''' a b AD AB) as d
  euclid_apply (line_from_points d c) as DC
  euclid_assert (|(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|)
  euclid_assert (|(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)|)
  euclid_apply (proposition_47 a d c AD DC AC)
  euclid_assert (|(d─c)| = |(b─c)|)
  euclid_apply (proposition_8 a b c a d c AB BC AC AD DC AC)
  euclid_finish


end Elements
