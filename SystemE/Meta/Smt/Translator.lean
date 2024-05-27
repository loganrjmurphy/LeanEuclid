import SystemE.Meta.Smt.Esmt
import SystemE.Meta.Smt.UniGeo
import SystemE.Theory.Relations
import SystemE.Theory.Sorts
import UniGeo.Relations
import Lean

set_option autoImplicit false

open Lean Elab Tactic Meta

namespace SystemE.Smt

abbrev TranslationResult α  := Except String α

/-- Write a ternary function over two fvars in SMTLIB format -/
def mkFvarOp2 (op : String) (v1 v2 : FVarId) : EsmtM String := do
  let nm1 ← getSanitizedName! v1
  let nm2 ← getSanitizedName! v2
  return s!"({op} {nm1} {nm2})"

/-- Write a ternary function over two fvars in SMTLIB format -/
def mkFvarOp3 (op : String) (v1 v2 v3 : FVarId) : EsmtM String := do
  let nm1 ← getSanitizedName! v1
  let nm2 ← getSanitizedName! v2
  let nm3 ← getSanitizedName! v3
  return s!"({op} {nm1} {nm2} {nm3})"

/-- Write a binary function over two exprs in SMTLIB format, using a srting-valued translator -/
def mkExprStrOp2  (translate : Expr → EsmtM (TranslationResult String)) (op : String) (l r : Expr) : EsmtM (TranslationResult String) := do
  match ← translate l , ← translate r with
  | .ok x, .ok y => return .ok s!"({op} {x} {y})"
  | .error m, _ => return .error m
  | _, .error m => return .error m

/-- Write a binary function over two exprs as an EAssertion -/
private def buildAssertionFrom (translate : Expr → EsmtM (TranslationResult String)) (C : String → String → EAssertion) (e₁ e₂ : Expr) : EsmtM (TranslationResult EAssertion) := do
  match (← translate e₁), (← translate e₂) with
  | .ok x, .ok y => return .ok <| C x y
  | .error m, _ => return .error m
  | _, .error m => return .error m

/-- Write a ternary function over two exprs as an EAssertion -/
private def buildAssertionFrom3 (f : Expr → EsmtM (TranslationResult String)) (C : String → String → String → EAssertion) (e₁ e₂ e₃: Expr) : EsmtM (TranslationResult EAssertion) := do
  match (← f e₁), (← f e₂), (← f e₃) with
  | .ok x, .ok y, .ok z => return .ok <| C x y z
  | .error e, _, _  => return .error e
  | _, .error e, _ => return .error e
  | _, _, .error e => return .error e

def translateNumeric (e: Expr) : EsmtM String :=
  match e.getAppFnArgs with
  | (``Zero.toOfNat0, _) => return "0.0"
  | (``instOfNat, #[_, .lit (.natVal n), _, _]) => return s!"{n}"
  | _ => throwError "[Smt.Translator] Improper numeric"

/-- Translate applications of metric functions (length, area etc.) over geometric objects-/
def translateMetric : Expr →  EsmtM (TranslationResult String)
| .app (.const ``Segment.length _ ) arg => do
    match  (← whnf arg).getAppFnArgs with
    | (``Segment.endpoints, #[(.fvar v1),(.fvar v2)]) => return .ok <| ← mkFvarOp2 "SegmentPP" v1 v2
    | _ => return  .error "[Smt.Translator] Improper arguments given to Segment.length, expected fvars"
| .app (.const ``Angle.degree _ ) arg => do
    match  (← whnf arg).getAppFnArgs with
    | (``Angle.ofPoints, #[(.fvar v1),(.fvar v2), (.fvar v3)]) => return .ok  <| ← mkFvarOp3 "AnglePPP" v1 v2 v3
    | (``Angle.Right, _) => return .ok "RightAngle"
    | _ => return  .error "[Smt.Translator] Improper input to Angle.degree"
| .app (.const ``Triangle.area _ ) arg => do
    match (← whnf arg).getAppFnArgs with
    | (``Triangle.ofPoints, #[(Expr.fvar v1),(Expr.fvar v2),(Expr.fvar v3)]) => return .ok  <| ← mkFvarOp3 "AreaPPP" v1 v2 v3
    | _ => return  .error "[Smt.Translator] Improper input to Triangle.area"
| e =>
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, _, e]) => return .ok <| ← translateNumeric e
  | (``Angle.Right, _) => return .ok "RightAngle"
  | _ => return .error s!"[Smt.Translator] Unknown metric operation {e}"

/-- Translate arithmetic expressions -/
partial def translateArith (e : Expr) : EsmtM (TranslationResult String) :=
match e.getAppFnArgs with
| (``HAdd.hAdd, #[_, _, _, _, l, r]) => mkExprStrOp2 translateArith "+" l r
| (``HMul.hMul, #[_, _, _, _, l, r]) => mkExprStrOp2 translateArith "*" l r
| (``HDiv.hDiv, #[_, _, _, _, l, r]) => mkExprStrOp2 translateArith "/" l r
| _ => translateMetric e



def translateGeoAux (e : Expr) : EsmtM  (TranslationResult String) :=
 match e.getAppFnArgs with
  | (``Angle.ofPoints, #[(.fvar v1),(.fvar v2),(.fvar v3)]) => return .ok  <| ← mkFvarOp3 "AnglePPP" v1 v2 v3
  | (``Triangle.ofPoints, #[(.fvar v1),(.fvar v2),(.fvar v3)]) => return .ok  <| ← mkFvarOp3 "AreaPPP" v1 v2 v3
  | x => return .error s!"[Smt.Translator] Expected geometric object, got {x}"

/-Translate geometric objects -/
def translateGeo : Expr →  EsmtM (TranslationResult String)
| .fvar v => return .ok <| ← getSanitizedName! v
| e => translateGeoAux e

/-- Translate a Lean Expression to a System E expression, which can then be exported in SMTLIB format.-/
partial def translateExpr (e : Expr) : EsmtM (TranslationResult EAssertion) := do
  match e with
  | .const `False _ => return .ok <| .neg .top
  | .const `True _ => return .ok .top
  | .mdata _ e' => translateExpr e'
  | .forallE nm τ P _ => translateArrow nm τ P
  | .app _ _ =>
    match e.getAppFnArgs with
     -- logical connectives + existential quantifiers
    | (``Or, #[l, r]) =>
      match (← translateExpr l), (← translateExpr r) with
      | .ok x, .ok y => return .ok <| .or x y
      | .error msg, _ => return .error msg
      | _, .error msg => return .error msg
    | (``And, #[l, r]) =>
      match (← translateExpr l), (← translateExpr r) with
      | .ok x, .ok y => return .ok <| .and x y
      | .error msg, _ => return .error msg
      | _, .error msg => return .error msg
    | (``Not, #[p]) =>
     match (← translateExpr p) with
        | .ok x => return .ok <| .neg x
        | .error k => return .error k
    | (``Exists, #[τ, .lam nm _ body _]) => translateExists nm τ body

    -- (In)Equalities over ℝ, i.e., arithmetical propositions
    | (``Eq, #[.const `Real [], l, r]) => buildAssertionFrom translateArith .eq l r
    | (``LT.lt,#[_, _, l, r]) =>  buildAssertionFrom translateArith .lt l r
    | (``LE.le, #[_, _, l, r]) => buildAssertionFrom translateArith .lte l r
    | (``GT.gt, #[_, _, l, r]) => buildAssertionFrom translateArith .gt l r
    | (``GE.ge, #[_, _, l, r]) => buildAssertionFrom  translateArith .gte l r
    | (``Ne, #[.const `Real [], l, r]) => buildAssertionFrom translateArith (fun s t => .neg (.eq s t)) l r

    -- (In)Equalities *not* over ℝ, i.e., (in)equalities between geometric objects
    | (``Ne, #[_, l, r]) => buildAssertionFrom translateGeo (fun s t => .neg (.eq s t)) l r
    | (``Eq, #[_ , l, r]) => buildAssertionFrom translateGeo .eq l r

    -- Geometric relations
    | (``Point.onLine, #[l, r]) => buildAssertionFrom translateGeo (fun s l => .erel (.OnL s l)) l r
    | (``Point.isCentre, #[l, r]) =>  buildAssertionFrom translateGeo (fun s l => .erel (.Centre s l)) l r
    | (``Point.onCircle, #[l, r]) =>  buildAssertionFrom translateGeo (fun s l => .erel (.OnC s l)) l r
    | (``Point.insideCircle, #[l, r]) =>  buildAssertionFrom translateGeo (fun s l => .erel (.InC s l)) l r
    | (``between, #[a, b, c]) => buildAssertionFrom3 translateGeo (fun x y z => .erel (.Between x y z)) a b c
    | (``Point.sameSide, #[a, b, c]) => buildAssertionFrom3 translateGeo (fun x y z =>  .erel (.SameSide x y z)) a b c
    | (``Circle.intersectsCircle, #[c, d]) => buildAssertionFrom translateGeo (fun s l => .erel (.IntersectsCC s l)) c d
    | (``Line.intersectsCircle, #[c, d]) => buildAssertionFrom translateGeo (fun s l => .erel (.IntersectsLC s l)) c d
    | (``Line.intersectsLine, #[c, d]) => buildAssertionFrom translateGeo (fun s l => .erel (.IntersectsLL s l)) c d

    -- Specialized UniGeo Relations, see `Smt.UniGeo`
    | (``Triangle.congruent, #[tr1, tr2]) =>
      match handleCongruentTriangle tr1 tr2 with
      | none => return .error "[Smt.Translator] Unexpected argument to Triangle.congruent"
      | some e => translateExpr e
    | (``Triangle.similar, #[tr1, tr2]) =>
      match handleSimilarTriangle tr1 tr2 with
      | none => return .error "[Smt.Translator] Unexpected argument to Triangle.similar"
      | some e => translateExpr e
    | (N, _) => return .error s!"[Smt.Translator] Unexpected application {N}"
  | E => return .error s!"[Smt.Translator] Unexpected expression {E}"
  where
  translateArrow (nm : Name) (τ P : Expr) : EsmtM (TranslationResult EAssertion) := do
    if !P.hasLooseBVars then -- not a forall
      match (← translateExpr τ), (← translateExpr P) with
      | .ok x, .ok y => return .ok <| EAssertion.imp x y
      | .error msg, _ => return .error msg
      | _, .error msg => return .error msg
    else
      let s ← Esmt.sanitize nm.toString
      let v := FVarId.mk nm
      let fv := Expr.fvar v
      Esmt.addVar (v) s
      let P := (P.instantiate #[fv])
      match (getSort? τ) with
      | none => return .error s!"[Smt.Translator] Unexpected Type {τ} ; be sure to only quantify over points, lines and circles"
      | some t => match (← translateExpr P) with
                | .ok x => return .ok <| .all (← getSanitizedName! v) t.toString x
                | .error e => return .error e

  translateExists (nm : Name) (τ P : Expr)  : EsmtM (TranslationResult EAssertion) := do
    let s ← Esmt.sanitize nm.toString
    let v := FVarId.mk nm
    let fv := Expr.fvar v
    Esmt.addVar (v) s
    let P := (P.instantiate #[fv])
    match getSort? τ with
    | some t =>
      match  (← translateExpr P) with
      | .ok x => return .ok <| .ex s t.toString x
      | .error e => return .error e
    | none => return .error s!"[Smt.Translator] Unexpected Type {τ} ; be sure to only quantify over points, lines and circles"

def isFalse : Expr → Bool
| .const `False _ => true
| .mdata _ e => isFalse e
| _ => false


def check {α : Type} (x: EsmtM (TranslationResult α)) : EsmtM α := do
  match ← x with
  | .ok a => return a
  | .error msg => throwError msg

/--
   Given a Expr `e` corresponding to the current target, add the negation of `e` to the SMT query.
   Note that if the goal is `False`, then this is a no-op
-/
def addGoal (Γ : Esmt) (e : Expr) : TacticM Esmt := do
  let e' ← instantiateMVars e
  if isFalse e' then return Γ
  else
    let a ← translateExpr e' |>.run' Γ |> check
    return {Γ with asserts := Γ.asserts.push $ EAssertion.neg a}

private def addSanitizedVarName (decl : LocalDecl) : EsmtM Unit := do
  let s := (← decl.fvarId.getUserName).toString
  let nm ← Esmt.sanitize s
  Esmt.addVar decl.fvarId nm

private def addEConst (decl : LocalDecl) (τ : Expr) : EsmtM Unit := do
  let x ← getSanitizedName! decl.fvarId
  let s := getSort! τ
  Esmt.addConstDecl ⟨x,s⟩

private def getEsmt : EsmtM Esmt := do
  let ctx ← getLCtx
  for decl in ctx do
    let τ ← instantiateMVars decl.type
    unless decl.kind != LocalDeclKind.default do
      if (← isProp τ) then -- translate propositions
        match ← translateExpr τ with
        | .ok a => Esmt.addAssertion a
        | .error msg => throwError msg
      else -- translate objects
        addSanitizedVarName decl
        addEConst decl τ
  get

def getESMTfromContext : TacticM Esmt :=
  withMainContext do
    getEsmt.run' {consts := #[], asserts := #[]}

end SystemE.Smt


syntax "translateGoal" : tactic

elab "translateGoal" : tactic =>
  withMainContext do
    let g ← getMainTarget
    let ctx ← SystemE.Smt.getESMTfromContext
    let e := Prod.fst (← (SystemE.Smt.translateExpr g).run ctx)
    dbg_trace e
