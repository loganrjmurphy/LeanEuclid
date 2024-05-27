import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr :=  q(∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ a ≠ b  →
  ∃ (l : Point), |(a─l)| = |(b─c)| ∧ a = b)

def groundE : Expr := q(∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ a ≠ b →
  ∃ (l : Point), |(a─l)| = |(b─c)|)

def main (args : List String) : IO Unit := do
    let x ← parseArgs args
    runE3fromIO groundE testE x

def wfCheck : IO Unit := WfChecker testE

-- #eval wfCheck

-- #eval main ["myTest", "full", "5", "30", "30", "E3/out/foobar.json"]

-- allowed forms:
--  last (and only last) elt of array is Prop
-- (0) <univ> <fml> "→"  <exist> <fml> (default)

--  final elt of array is False
-- (1) <univ> "¬" <fml>
-- also check that <univ> <fml> "→"  "False" parses to this

-- canonical LHS, RHS is implication with RRHS False
-- (2) <univ> <fml> "→" "¬" <exist> <fml>
-- also check that <univ> <fml> "→"  <exist> <fml> "→" "False"

-- shouldn't need these, but here they are:

-- last Elt of array is not Prop
-- (3) <univ> <fml>
-- (4) <univ> <exist> <fml>


-- def test1 : Expr := q(
--   ∀ (a b c d : Point) (AB AC CB  CD : Line),
--   (distinctPointsOnLine a b AB ∧
--   distinctPointsOnLine a c AC ∧
--   distinctPointsOnLine c b CB ∧
--   a.sameSide b CD ∧ d.sameSide b AC ∧
--   (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|)) → False)


-- def test1neg : Expr := q(
--   ∀ (a b c d : Point) (AB AC CB  CD : Line),
--   ¬ (distinctPointsOnLine a b AB ∧
--   distinctPointsOnLine a c AC ∧
--   distinctPointsOnLine c b CB ∧
--   a.sameSide b CD ∧ d.sameSide b AC ∧
--   (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|)))


-- def test4 : Expr := q(
--     ∀ (A B C D : Point) (AB BD CD : Line),
--     Point.onLine A AB ∧
--     Point.onLine B AB ∧
--     Point.onLine C AB ∧
--     Point.onLine D AB ∧
--      twoLinesIntersectAtPoint BD CD D →
--      (∃ (E : Point) (AE BE DE : Line), distinctPointsOnLine A E AE ∧ distinctPointsOnLine B E BE ∧ distinctPointsOnLine D E DE ∧ Point.onLine E AB ∧ Point.sameSide C E AB))



-- def test3 : Expr := q(∀ (A B C D : Point) (AB AC BD CD : Line), Point.onLine A AB ∧ Point.onLine B AB ∧ Point.onLine C AB ∧ Point.onLine D AB ∧ Point.sameSide C D AB ∧ distinctPointsOnLine A B AB ∧ distinctPointsOnLine A C AC ∧ distinctPointsOnLine B C AC ∧ distinctPointsOnLine A D BD ∧ distinctPointsOnLine B D BD ∧ |(A─C)| = |(A─D)| ∧ |(B─C)| = |(B─D)| ∧ twoLinesIntersectAtPoint AC CD C ∧ twoLinesIntersectAtPoint BD CD D → ¬(∃ (E : Point) (AE BE DE : Line), distinctPointsOnLine A E AE ∧ distinctPointsOnLine B E BE ∧ distinctPointsOnLine D E DE ∧ Point.onLine E AB ∧ Point.sameSide C E AB ∧ |(A─E)| = |(A─C)| ∧ |(B─E)| = |(B─C)|))

-- def main  : IO Unit :=
--   runEvalFromIO test3 test3 default

-- #eval main
