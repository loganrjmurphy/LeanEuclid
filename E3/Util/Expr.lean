import E3.Data.BoundVars
import E3.Data.EvalCtx
import E3.Data.Config
import Lean
set_option autoImplicit false

open Lean Meta SystemE.Smt

/- Miscellaneous helper functions for dealing with `Expr` and related types -/

def getConsequentOf : Expr → MetaM Expr :=
λ e => forallTelescopeReducing e (λ _ x => return x)

def getExprName (n : ℕ) : Expr → MetaM (FVarId × String)
| .fvar v => do
  match ← v.getUserName with
  | .anonymous => return (v, s!"v_{n}")
  | nm => return ⟨v, nm.toString⟩
| x => throwError m!"[E3] error: Expected FVar, got {x}"

def addVarName (v : FVarId) (s : String) : EsmtM Unit := do
  let nm ← Esmt.sanitize s
  Esmt.addVar v nm

def addBvars :  Esmt → List EConst → MetaM Esmt
| x, [] => pure x
| x, ⟨nm, _⟩::t => do
  let fv : FVarId := .mk (.str .anonymous nm)
  let x' ← Prod.snd <$> StateT.run (addVarName fv nm) x
  addBvars x' t

def getConsequent (e : Expr) : MetaM Expr := do
  let e : Expr ← forallTelescopeReducing e (λ _ e => return e)
  return e

/-- Add syntactic guards to names of variables to avoid name capture when rewriting-/
def renameBVars (e : Expr) : Expr :=
  match e with
  | .app fn arg => .app (renameBVars fn) (renameBVars arg)
  | .lam n ty bd bi =>
    .lam (addGuard n) (renameBVars ty) (renameBVars bd) bi
  | .forallE n ty bd bi =>
    .forallE (addGuard n) (renameBVars ty) (renameBVars bd) bi
  | e => e
 where addGuard (nm : Name) : Name := s!"grd_{nm}"

def mergeMaps
  -- a mapping from test expr fvarIds to Strings
  (testMap : HashMap FVarId String)
  -- mapping from test strings to ground strings
  (swap : HashMap String String)
  -- output: Mapping from test expr fvarIds to ground strings
  : MetaM (HashMap FVarId String) := do
  let mut m₃ : HashMap FVarId String := {}
  let keys := testMap.toList.map Prod.fst
  for x in keys do
    match testMap[x] with
    | some s => match swap[s] with | some t => m₃ := m₃.insert x t | _ => continue
    | _ => continue
  return m₃



/-- Unfold abbreviations before invoking E3 -/

def GeoAbbrevs : List Name :=
  [
    `formParallelogram,
    `formTriangle,
    `formRectilinearAngle,
    `twoLinesIntersectAtPoint,
    `formQuadrilateral,
    `quadrilateralAnglesSum,
    `distinctPointsOnLine,
    `Point.opposingSides,
    `Point.collinear
  ]

def unfoldGeoAbbrevs (e : Expr) : MetaM Expr :=
  GeoAbbrevs.foldlM (λ nm x => return Simp.Result.expr <| ← unfold nm x) e

def preprocessExpr (ground test : Expr) : MetaM (Expr × Expr ) := do
 MetaM.run' do
          let eg ← unfoldGeoAbbrevs ground
          let et ← unfoldGeoAbbrevs test
          return (eg, et)
