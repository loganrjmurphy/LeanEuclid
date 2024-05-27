import Smt.Solver

abbrev PointT := (Smt.Term.literalT "Point")
abbrev BoolT := (Smt.Term.literalT "Bool")
abbrev LineT := (Smt.Term.literalT "Line")
abbrev CircleT := (Smt.Term.literalT "Circle")
abbrev RealT := (Smt.Term.literalT "Real")


-- Sorts, Relations and Inference rules
def euclidTheory : List Smt.Command := [
  -- Sorts.
  (Smt.Command.declareSort "Point" 0),
  (Smt.Command.declareSort "Line" 0),
  (Smt.Command.declareSort "Circle" 0),
  -- Predicates.
  (Smt.Command.declareFun "Between" [PointT, PointT, PointT] BoolT),
  (Smt.Command.declareFun "OnL" [PointT, LineT] BoolT),
  (Smt.Command.declareFun "OnC" [PointT, CircleT] BoolT),
  (Smt.Command.declareFun "Inside" [PointT, CircleT] BoolT),
  (Smt.Command.declareFun "Centre" [PointT, CircleT] BoolT),
  (Smt.Command.declareFun "SameSide" [PointT, PointT, LineT] BoolT),
  (Smt.Command.declareFun "IntersectsLL" [LineT, LineT] BoolT),
  (Smt.Command.declareFun "IntersectsLC" [LineT, CircleT] BoolT),
  (Smt.Command.declareFun "IntersectsCC" [CircleT, CircleT] BoolT),
  -- Functions.
  (Smt.Command.declareFun "SegmentPP" [PointT, PointT] RealT),
  (Smt.Command.declareFun "AnglePPP" [PointT, PointT, PointT] RealT),
  (Smt.Command.declareFun "AreaPPP" [PointT, PointT, PointT] RealT),
  (Smt.Command.declare "RightAngle" (Smt.Term.symbolT "Real")),
  -- two_points_determine_line
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (L Line) (M Line))
    (=>
      (and (not (= a b)) (OnL a L) (OnL b L) (OnL a M) (OnL b M))
      (= L M)
    )
  )")),
  -- centre_unique
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (alpha Circle))
    (=>
      (and (Centre a alpha) (Centre b alpha))
      (= a b)
    )
  )")),
  -- center_inside_circle
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (alpha Circle))
    (=>
      (Centre a alpha)
      (Inside a alpha)
    )
  )")),
  -- inside_not_on_circle
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (alpha Circle))
    (=>
      (Inside a alpha)
      (not (OnC a alpha))
    )
  )")),
  -- between_symm
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (=>
      (Between a b c)
      (and
        (Between c b a)
        (not (= a b))
        (not (= a c))
        (not (Between b a c))
      )
    )
  )")),
  -- between_same_line_out
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and (Between a b c) (OnL a L) (OnL b L))
      (OnL c L)
    )
  )")),
  -- between_same_line_in
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and (Between a b c) (OnL a L) (OnL c L))
      (OnL b L)
    )
  )")),
  -- between_trans_in
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point))
    (=>
      (and (Between a b c) (Between a d b))
      (Between a d c)
    )
  )")),
  -- between_trans_out
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point))
    (=>
      (and (Between a b c) (Between b c d))
      (Between a b d)
    )
  )")),
  -- between_points
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and
        (not (= a b))
        (not (= b c))
        (not (= c a))
        (OnL a L)
        (OnL b L)
        (OnL c L)
      )
      (or
        (Between a b c)
        (Between b a c)
        (Between a c b)
      )
    )
  )")),
  -- between_not_trans
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point))
    (=>
      (and (Between a b c) (Between a b d))
      (not (Between c b d))
    )
  )")),
  -- same_side_rfl
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (L Line))
    (=>
      (not (OnL a L))
      (SameSide a a L)
    )
  )")),
  -- same_side_symm
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (L Line))
    (=>
      (SameSide a b L)
      (SameSide b a L)
    )
  )")),
  -- same_side_not_on_line
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (L Line))
    (=>
      (SameSide a b L)
      (not (OnL a L))
    )
  )")),
  -- same_side_trans
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and (SameSide a b L) (SameSide a c L))
      (SameSide b c L)
    )
  )")),
  -- same_side_pigeon_hole
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and
        (not (OnL a L))
        (not (OnL b L))
        (not (OnL c L))
      )
      (or
        (SameSide a b L)
        (SameSide a c L)
        (SameSide b c L)
      )
    )
  )")),
  -- pasch_1
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and (Between a b c) (SameSide a c L))
      (SameSide a b L)
    )
  )")),
  -- pasch_2
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and (Between a b c) (OnL a L) (not (OnL b L)))
      (SameSide b c L)
    )
  )")),
  -- pasch_3
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and (Between a b c) (OnL b L))
      (not (SameSide a c L))
    )
  )")),
  -- pasch_4
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line) (M Line))
    (=>
      (and
        (not (= L M))
        (OnL b L)
        (OnL b M)
        (not (= a c))
        (OnL a M)
        (OnL c M)
        (not (= a b))
        (not (= c b))
        (not (SameSide a c L))
      )
      (Between a b c)
    )
  )")),
  -- triple_incidence_1
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point))
    (=>
      (and
        (OnL a L)
        (OnL a M)
        (OnL a N)
        (OnL b L)
        (OnL c M)
        (OnL d N)
        (SameSide c d L)
        (SameSide b c N)
      )
      (not (SameSide b d M))
    )
  )")),
  -- triple_incidence_2
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point))
    (=>
      (and
        (OnL a L)
        (OnL a M)
        (OnL a N)
        (OnL b L)
        (OnL c M)
        (OnL d N)
        (SameSide c d L)
        (not (SameSide b d M))
        (not (OnL d M))
        (not (= b a))
      )
      (SameSide b c N)
    )
  )")),
  -- triple_incidence_3
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point) (e Point))
    (=>
      (and
        (OnL a L)
        (OnL a M)
        (OnL a N)
        (OnL b L)
        (OnL c M)
        (OnL d N)
        (SameSide c d L)
        (SameSide b c N)
        (SameSide d e M)
        (SameSide c e N)
      )
      (SameSide c e L)
    )
  )")),
  -- circle_line_intersections
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line) (alpha Circle))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (OnL c L)
        (Inside a alpha)
        (OnC b alpha)
        (OnC c alpha)
        (not (= b c))
      )
      (Between b a c)
    )
  )")),
  -- circle_points_between
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (alpha Circle))
    (=>
      (and
        (or (Inside a alpha) (OnC a alpha))
        (or (Inside b alpha) (OnC b alpha))
        (Between a c b)
      )
      (Inside c alpha)
    )
  )")),
  -- circle_points_extend
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (alpha Circle))
    (=>
      (and
        (or (Inside a alpha) (OnC a alpha))
        (not (Inside c alpha))
        (Between a c b)
      )
      (and
        (not (Inside b alpha))
        (not (OnC b alpha))
      )
    )
  )")),
  -- circles_intersections_diff_side
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (alpha Circle) (beta Circle) (L Line))
    (=>
      (and
        (not (= alpha beta))
        (OnC c alpha)
        (OnC c beta)
        (OnC d alpha)
        (OnC d beta)
        (not (= c d))
        (Centre a alpha)
        (Centre b beta)
        (OnL a L)
        (OnL b L)
      )
      (not (SameSide c d L))
    )
  )")),
  -- intersection_lines_opposing
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (L Line) (M Line))
    (=>
      (and
        (not (OnL a L))
        (not (OnL b L))
        (not (SameSide a b L))
        (OnL a M)
        (OnL b M)
      )
      (IntersectsLL L M)
    )
  )")),
  -- intersection_lines_common_point
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (L Line) (M Line))
    (=>
      (and (OnL a L) (OnL a M) (not (= L M)))
      (IntersectsLL L M)
    )
  )")),
  -- parallel_line_unique
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (L Line) (M Line) (N Line))
    (=>
      (and
        (not (OnL a L))
        (OnL a M)
        (OnL a N)
        (not (IntersectsLL L M))
        (not (IntersectsLL L N))
      )
      (= M N)
    )
  )")),
  -- intersection_symm
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((L Line) (M Line))
    (=>
      (IntersectsLL L M)
      (IntersectsLL M L)
    )
  )")),
  -- intersection_circle_line_1
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (alpha Circle) (L Line))
    (=>
      (and
        (or (OnC a alpha) (Inside a alpha))
        (or (OnC b alpha) (Inside b alpha))
        (not (OnL a L))
        (not (OnL b L))
        (not (SameSide a b L))
      )
      (IntersectsLC L alpha)
    )
  )")),
  -- intersection_circle_line_2
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (alpha Circle) (L Line))
    (=>
      (and (Inside a alpha) (OnL a L))
      (IntersectsLC L alpha)
    )
  )")),
  -- intersection_circle_circle_1
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (alpha Circle) (beta Circle))
    (=>
      (and
        (or (OnC a alpha) (Inside a alpha))
        (or (OnC b alpha) (Inside b alpha))
        (Inside a beta)
        (not (Inside b beta))
        (not (OnC b beta))
      )
      (IntersectsCC alpha beta)
    )
  )")),
  -- intersection_circle_circle_2
  (Smt.Command.assert (Smt.Term.literalT
  "(forall ((a Point) (b Point) (alpha Circle) (beta Circle))
    (=>
      (and
        (OnC a alpha)
        (Inside b alpha)
        (Inside a beta)
        (OnC b beta)
      )
      (IntersectsCC alpha beta)
    )
  )")),
  -- parallelogram_same_side
  /-
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (AB Line) (CD Line) (AC Line) (BD Line))
    (=>
      (and
        (OnL a AB)
        (OnL b AB)
        (OnL c CD)
        (OnL d CD)
        (OnL a AC)
        (OnL c AC)
        (not (= b d))
        (OnL b BD)
        (OnL d BD)
        (SameSide c d AB)
        (not (IntersectsLL AB CD))
        (not (IntersectsLL AC BD))
      )
      (and (SameSide b d AC) (SameSide c d AB) (SameSide a b CD))
    )
  )")),
  -/
  -- zero_segment_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point))
    (=>
      (= (SegmentPP a b) 0.0)
      (= a b)
    )
  )")),
  -- zero_segment_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point))
    (=>
      (= a b)
      (= (SegmentPP a b) 0.0)
    )
  )")),
  -- segment_gte_zero
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point))
    (>= (SegmentPP a b) 0.0)
  )")),
  -- segment_symmetric
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point))
    (= (SegmentPP a b) (SegmentPP b a))
  )")),
  -- angle_symm
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (=>
      (and
        (not (= a b))
        (not (= b c))
      )
      (= (AnglePPP a b c) (AnglePPP c b a))
    )
  )")),
  -- angle_range
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (=>
      (and
        (not (= a b))
        (not (= b c))
      )
      (and
        (>= (AnglePPP a b c) 0.0)
        (<= (AnglePPP a b c) (+ RightAngle RightAngle))
      )
    )
  )")),
  -- degenerated_area
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point))
    (= (AreaPPP a a b) 0.0)
  )")),
  -- area_gte_zero
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (>= (AreaPPP a b c) 0.0)
  )")),
  -- area_symm_1
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (= (AreaPPP a b c) (AreaPPP c a b))
  )")),
  -- area_symm_2
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (= (AreaPPP a b c) (AreaPPP a c b))
  )")),
  -- area_congruence
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (e Point) (f Point))
    (=>
      (and
        (= (SegmentPP a b) (SegmentPP d e))
        (= (SegmentPP b c) (SegmentPP e f))
        (= (SegmentPP c a) (SegmentPP f d))
        (= (AnglePPP a b c) (AnglePPP d e f))
        (= (AnglePPP b c a) (AnglePPP e f d))
        (= (AnglePPP c a b) (AnglePPP f d e))
      )
      (= (AreaPPP a b c) (AreaPPP d e f))
    )
  )")),
  -- between_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (=>
      (Between a b c)
      (= (+ (SegmentPP a b) (SegmentPP b c)) (SegmentPP a c))
    )
  )")),
  -- equal_circles
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (alpha Circle) (beta Circle))
    (=>
      (and
        (Centre a alpha)
        (Centre a beta)
        (OnC b alpha)
        (OnC c beta)
        (= (SegmentPP a b) (SegmentPP a c))
      )
      (= alpha beta)
    )
  )")),
  -- point_on_circle_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (alpha Circle))
    (=>
      (and
        (Centre a alpha)
        (OnC b alpha)
        (= (SegmentPP a c) (SegmentPP a b))
      )
      (OnC c alpha)
    )
  )")),
  -- point_on_circle_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (alpha Circle))
    (=>
      (and
        (Centre a alpha)
        (OnC b alpha)
        (OnC c alpha)
      )
      (= (SegmentPP a c) (SegmentPP a b))
    )
  )")),
  -- point_in_circle_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (alpha Circle))
    (=>
      (and
        (Centre a alpha)
        (OnC b alpha)
        (< (SegmentPP a c) (SegmentPP a b))
      )
      (Inside c alpha)
    )
  )")),
  -- point_in_circle_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (alpha Circle))
    (=>
      (and
        (Centre a alpha)
        (OnC b alpha)
        (Inside c alpha)
      )
      (< (SegmentPP a c) (SegmentPP a b))
    )
  )")),
  -- degenerated_angle_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and
        (not (= a b))
        (not (= a c))
        (OnL a L)
        (OnL b L)
        (OnL c L)
        (not (Between b a c))
      )
      (= (AnglePPP b a c) 0.0)
    )
  )")),
  -- degenerated_angle_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and
        (not (= a b))
        (not (= a c))
        (OnL a L)
        (OnL b L)
        (= (AnglePPP b a c) 0.0)
      )
      (and
        (OnL c L)
        (not (Between b a c))
      )
    )
  )")),
  /-
  -- angle_superposition
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
    (!
      (=>
        (and
          (OnL a L)
          (OnL b L)
          (not (= a b))
          (not (= d a))
          (SameSide c d L)
          (= (AnglePPP b a c) (AnglePPP b a d))
          (= (SegmentPP a c) (SegmentPP a d))
        )
        (= c d)
      )
    :pattern ((OnL a L) (OnL b L) (SameSide c d L) (= (AnglePPP b a c) (AnglePPP b a d)) (= (SegmentPP a c) (SegmentPP a d))) )
  )")),
  -/
  -- sum_angles_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line))
    (=>
      (and
        (OnL a L)
        (OnL a M)
        (OnL b L)
        (OnL c M)
        (not (= a b))
        (not (= a c))
        (not (OnL d L))
        (not (OnL d M))
        (not (= L M))
        (= (AnglePPP b a c) (+ (AnglePPP b a d) (AnglePPP d a c)))
      )
      (and (SameSide b d M) (SameSide c d L))
    )
  )")),
  -- sum_angles_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line))
    (=>
      (and
        (OnL a L)
        (OnL a M)
        (OnL b L)
        (OnL c M)
        (not (= a b))
        (not (= a c))
        (not (OnL d L))
        (not (OnL d M))
        (not (= L M))
        (SameSide b d M)
        (SameSide c d L)
      )
      (= (AnglePPP b a c) (+ (AnglePPP b a d) (AnglePPP d a c)))
    )
  )")),
  -- perpendicular_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (Between a c b)
        (not (OnL d L))
        (= (AnglePPP a c d) (AnglePPP d c b))
      )
      (= (AnglePPP a c d) RightAngle)
    )
  )")),
  -- perpendicular_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (Between a c b)
        (not (OnL d L))
        (= (AnglePPP a c d) RightAngle)
      )
      (= (AnglePPP a c d) (AnglePPP d c b))
    )
  )")),
  -- flat_angle_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (=>
      (and
        (not (= a b))
        (not (= b c))
        (= (AnglePPP a b c) (+ RightAngle RightAngle))
      )
      (Between a b c)
    )
  )")),
  -- flat_angle_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point))
    (=>
      (Between a b c)
      (= (AnglePPP a b c) (+ RightAngle RightAngle))
    )
  )")),
  -- equal_angles
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (e Point) (c Point) (f Point) (L Line) (M Line))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (OnL e L)
        (OnL a M)
        (OnL c M)
        (OnL f M)
        (not (= b a))
        (not (= e a))
        (not (= c a))
        (not (= f a))
        (not (Between b a e))
        (not (Between c a f))
      )
      (= (AnglePPP b a c) (AnglePPP e a f))
    )
  )")),
  -- lines_intersect
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line) (N Line))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (OnL b M)
        (OnL c M)
        (OnL c N)
        (OnL d N)
        (not (= b c))
        (SameSide a d M)
        (< (+ (AnglePPP a b c) (AnglePPP b c d)) (+ RightAngle RightAngle))
      )
      (exists ((e Point))
        (and
          (OnL e L)
          (OnL e N)
          (SameSide e a M)
        )
      )
    )
  )")),
  -- degenerated_area_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (not (= a b))
        (= (AreaPPP a b c) 0.0)
      )
      (OnL c L)
    )
  )")),
  -- degenerated_area_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (L Line))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (not (= a b))
        (OnL c L)
      )
      (= (AreaPPP a b c) 0.0)
    )
  )")),
  -- sum_areas_if
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (OnL c L)
        (not (= a b))
        (not (= a c))
        (not (= b c))
        (not (OnL d L))
        (Between a c b)
      )
      (= (+ (AreaPPP a c d) (AreaPPP d c b)) (AreaPPP a d b))
    )
  )")),
  -- sum_areas_onlyif
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
    (=>
      (and
        (OnL a L)
        (OnL b L)
        (OnL c L)
        (not (= a b))
        (not (= a c))
        (not (= b c))
        (not (OnL d L))
        (= (+ (AreaPPP a c d) (AreaPPP d c b)) (AreaPPP a d b))
      )
      (Between a c b)
    )
  )")),
  -- parallelogram_area
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (AB Line) (CD Line) (AC Line) (BD Line))
    (=>
      (and
        (OnL a AB)
        (OnL b AB)
        (OnL c CD)
        (OnL d CD)
        (OnL a AC)
        (OnL c AC)
        (not (= b d))
        (OnL b BD)
        (OnL d BD)
        (SameSide a c BD)
        (not (IntersectsLL AB CD))
        (not (IntersectsLL AC BD))
      )
      (=
        (+ (AreaPPP a c d) (AreaPPP a d b))
        (+ (AreaPPP b a c) (AreaPPP b c d))
      )
    )
  )")),
  -- sum_parallelograms_area
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (e Point) (f Point) (AB Line) (CD Line) (AC Line) (BD Line))
    (=>
      (and
        (OnL a AB)
        (OnL b AB)
        (OnL c CD)
        (OnL d CD)
        (OnL a AC)
        (OnL c AC)
        (not (= b d))
        (OnL b BD)
        (OnL d BD)
        (SameSide a c BD)
        (not (IntersectsLL AB CD))
        (not (IntersectsLL AC BD))
        (Between a e b)
        (Between c f d)
      )
      (=
        (+ (AreaPPP a c f) (AreaPPP a f e) (AreaPPP e f d) (AreaPPP e d b))
        (+ (AreaPPP a c d) (AreaPPP a d b))
      )
    )
  )")),
  -- rectangle_area
  /-
  (Smt.Command.assert (Smt.Term.literalT "
  (forall ((a Point) (b Point) (c Point) (d Point) (AB Line) (CD Line) (AC Line) (BD Line))
    (=>
      (and
        (OnL a AB)
        (OnL b AB)
        (OnL c CD)
        (OnL d CD)
        (OnL a AC)
        (OnL c AC)
        (not (= b d))
        (OnL b BD)
        (OnL d BD)
        (SameSide a c BD)
        (not (IntersectsLL AB CD))
        (not (IntersectsLL AC BD))
        (= (AnglePPP a c d) RightAngle)
      )
      (and
        (=
          (+ (AreaPPP a c d) (AreaPPP a b d))
          (* (SegmentPP a b) (SegmentPP a c))
        )
        (=
          (+ (AreaPPP b a c) (AreaPPP b d c))
          (* (SegmentPP a b) (SegmentPP a c))
        )
      )
    )
  )")),
  -/
]

-- Construction Rules
def euclidConstructionRulesFull : List Smt.Command := [
  (Smt.Command.assert (Smt.Term.literalT "
       (exists ((a Point))  true)
  ")),
(Smt.Command.assert (Smt.Term.literalT "
    (forall ((a Point))
        (exists ((b Point))
            (not (= b a))
        )
    )")),


(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line))
        (exists ((a Point))
            (OnL a L)
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (a Point))
        (exists ((b Point))
            (and
                (OnL b L)
                (not (= b a))
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point) (c Point))
        (=>
            (and
                (OnL b L)
                (OnL c L)
                (not (= b c))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
                    (Between b a c)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (M Line) (b Point) (c Point))
        (=>
            (and
                (OnL b L)
                (OnL c L)
                (not (= b c))
                (not (= L M))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
                    (Between b a c)
                    (not (OnL a M))
                )
            )
        )
    )")),


(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point) (c Point))
        (=>
            (and
                (OnL b L)
                (OnL c L)
                (not (= b c))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
                    (Between b c a)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (M Line) (b Point) (c Point))
        (=>
            (and
                (OnL b L)
                (OnL c L)
                (not (= b c))
                (not (= L M))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
                    (Between b c a)
                    (not (OnL a M))
                )
            )
        )
    )")),
(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point))
        (=>
            (not (OnL b L))
            (exists ((a Point))
                (SameSide a b L)
            )
        )
    )")),


(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point) (c Point))
        (=>
            (not (OnL b L))
            (exists ((a Point))
                (and
                    (not (= a c))
                    (SameSide a b L)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point))
        (=>
            (not (OnL b L))
            (exists ((a Point))
                (and
                    (not (OnL a L))
                    (not (SameSide a b L))
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point) (c Point))
        (=>
            (not (OnL b L))
            (exists ((a Point))
                (and
                    (not (= a c))
                    (not (OnL a L))
                    (not (SameSide a b L))
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle))
        (exists ((a Point))
            (OnC a alpha)
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (b Point))
        (exists ((a Point))
            (and
                (not (= a b))
                (OnC a alpha)
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle))
        (exists ((a Point))
            (Inside a alpha)
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (b Point))
        (exists ((a Point))
            (and
                (not (= a b))
                (Inside a alpha)
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle))
        (exists ((a Point))
            (and
                (not (OnC a alpha))
                (not (Inside a alpha))
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (b Point))
        (exists ((a Point))
            (and
                (not (= a b))
                (not (OnC a alpha))
                (not (Inside a alpha))
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((a Point) (b Point))
        (=>
            (not (= a b))
            (exists ((L Line))
                (and
                    (OnL a L)
                    (OnL b L)
                )
            )
        )
    )")),


-- intersections
(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (M Line))
        (=>
            (IntersectsLL L M)
            (exists ((a Point))
                (and
                    (OnL a L)
                    (OnL a M)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (L Line))
        (=>
            (IntersectsLC L alpha)
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (L Line))
        (=>
            (IntersectsLC L alpha)
            (exists ((a Point) (b Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
                    (OnC b alpha)
                    (OnL b L)
                    (not (= a b))
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (L Line) (b Point) (c Point))
        (=>
            (and
                (Inside b alpha)
                (OnL b L)
                (not (Inside c alpha))
                (not (OnC c alpha))
                (OnL c L)
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
                    (Between b a c)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (L Line) (b Point) (c Point))
        (=>
            (and
                (Inside b alpha)
                (OnL b L)
                (not (= c b))
                (OnL c L)
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
                    (Between a b c)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (L Line) (b Point) (c Point))
        (=>
            (and
                (Inside b alpha)
                (OnL b L)
                (not (= c b))
                (OnL c L)
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
                    (Between a b c)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (beta Circle))
        (=>
            (IntersectsCC alpha beta)
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnC a beta)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (beta Circle))
        (=>
            (IntersectsCC alpha beta)
            (exists ((a Point) (b Point))
                (and
                    (OnC a alpha)
                    (OnC a beta)
                    (OnC b alpha)
                    (OnC b beta)
                    (not (= a b))
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (beta Circle) (b Point) (c Point) (d Point) (L Line))
        (=>
            (and
                (IntersectsCC alpha beta)
                (Centre c alpha)
                (Centre c beta)
                (OnL c L)
                (OnL d L)
                (not (OnL b L))
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnC a beta)
                    (SameSide a b L)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle) (beta Circle) (b Point) (c Point) (d Point) (L Line))
        (=>
            (and
                (IntersectsCC alpha beta)
                (Centre c alpha)
                (Centre c beta)
                (OnL c L)
                (OnL d L)
                (not (OnL b L))
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnC a beta)
                    (not (SameSide a b L))
                    (not (OnL a L))
                )
            )
        )
    )")),
]


def euclidConstructionRulesShort : List Smt.Command := [
    (Smt.Command.assert (Smt.Term.literalT "
       (exists ((a Point))  true)
  ")),
(Smt.Command.assert (Smt.Term.literalT "
    (forall ((a Point))
        (exists ((b Point))
            (not (= b a))
        )
    )")),


(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line))
        (exists ((a Point))
            (OnL a L)
        )
    )")),


(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point) (c Point))
        (=>
            (and
                (OnL b L)
                (OnL c L)
                (not (= b c))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
                    (Between b a c)
                )
            )
        )
    )")),


(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point) (c Point))
        (=>
            (and
                (OnL b L)
                (OnL c L)
                (not (= b c))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
                    (Between b c a)
                )
            )
        )
    )")),

-- (Smt.Command.assert (Smt.Term.literalT "
--     (forall ((L Line) (b Point))
--         (=>
--             (not (OnL b L))
--             (exists ((a Point))
--                 (SameSide a b L)
--             )
--         )
--     )")),


(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point) (c Point))
        (=>
            (not (OnL b L))
            (exists ((a Point))
                (and
                    (not (= a c))
                    (SameSide a b L)
                )
            )
        )
    )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (b Point))
        (=>
            (not (OnL b L))
            (exists ((a Point))
                (and
                    (not (OnL a L))
                    (not (SameSide a b L))
                )
            )
        )
    )")),

-- (Smt.Command.assert (Smt.Term.literalT "
--     (forall ((L Line) (b Point) (c Point))
--         (=>
--             (not (OnL b L))
--             (exists ((a Point))
--                 (and
--                     (not (= a c))
--                     (not (OnL a L))
--                     (not (SameSide a b L))
--                 )
--             )
--         )
--     )")),

(Smt.Command.assert (Smt.Term.literalT "
    (forall ((alpha Circle))
        (exists ((a Point))
            (OnC a alpha)
        )
    )")),



(Smt.Command.assert (Smt.Term.literalT "
    (forall ((a Point) (b Point))
        (=>
            (not (= a b))
            (exists ((L Line))
                (and
                    (OnL a L)
                    (OnL b L)
                )
            )
        )
    )")),


-- intersections
(Smt.Command.assert (Smt.Term.literalT "
    (forall ((L Line) (M Line))
        (=>
            (IntersectsLL L M)
            (exists ((a Point))
                (and
                    (OnL a L)
                    (OnL a M)
                )
            )
        )
    )")),



-- intersections

]
