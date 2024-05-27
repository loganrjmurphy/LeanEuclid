import E3.Data.BoundVars
import E3.Data.EvalCtx
import E3.Data.Config
import E3.Util.Expr
import Lean
import Qq
set_option autoImplicit false

open Qq Lean
open Lean Meta SystemE.Smt

def collectFvar (fv : Expr) : EsmtM Unit := do
  match getSort? (← inferType fv) with
    | some s =>
        let ⟨v, nm⟩ ← getExprName (← Esmt.getVarNum) fv
        addVarName v nm
        Esmt.addConstDecl ⟨nm,s⟩
    | none => return ()

private def splitExprAndCollectBVars (arr : Array Expr ) (e : Expr) : EsmtM (Expr × Expr) :=
do
  arr.forM collectFvar
  let antecedent ← inferType arr[arr.size-1]!
  return (antecedent,e)


private def splitNegativeExprAndCollectBVars (arr : Array Expr ) (_ : Expr) : EsmtM (Expr × Expr) :=
do
  if arr.size < 2 then throwError "[E3] error: formula not well-formed (too few arrows)"
  arr.forM collectFvar
  let antecedent ← inferType arr[arr.size-2]!
  let consequent : Expr := .app (.const `Not []) (← inferType arr[arr.size-1]!)
  return (antecedent, consequent)


def splitExpr (isNegation : Bool) (e : Expr) : EsmtM (Expr × Expr × Esmt) := do
  if isNegation then
    let (lhs, rhs) ← forallTelescopeReducing e splitNegativeExprAndCollectBVars
    let Γ ← get
    return ⟨lhs,rhs,Γ⟩
  else
    let (lhs,rhs) ← forallTelescopeReducing e splitExprAndCollectBVars
    let Γ ← get
    return ⟨lhs,rhs,Γ⟩

def runAndGetCtx {α : Type} (ctx : Esmt) (f : EsmtM α)  : MetaM Esmt :=
  Prod.snd <$> f.run ctx

/-- Iteratively collect  and instantiate the existentially bound variables in an expression,
   while updating the SMT translation context-/
partial def getExistVarsAux : List EConst → Esmt → Expr → MetaM (Expr × List EConst × Esmt)
| cs, ctx₀, e => do
  -- dbg_trace e
  match e.getAppFnArgs with
  | (``Exists, #[τ, .lam nm _ body _]) =>
    match getSort? τ  with
    | some s => do
        let s' ← SystemE.Smt.Esmt.sanitize nm.toString
        let fv := FVarId.mk s'
        let body := body.instantiate #[.fvar fv]
        let ctx₁ ← runAndGetCtx ctx₀ <| addVarName fv s'
        let ctx₂ ← runAndGetCtx ctx₁ <| Esmt.addConstDecl ⟨s',s⟩
        let cs' := ⟨s',s⟩::cs
        -- dbg_trace cs'
        getExistVarsAux cs' ctx₂ body
    | none => return ⟨e,cs,ctx₀⟩
  | _ => return ⟨e,cs,ctx₀⟩

/- Given an SMT translation context `Γ` and type of the form `∃ x1 .. xn, P`, returns `(P, [x1, ... xn], Γ')`, where
   `Γ'` is `Γ` with the addition of each `xi` as a new free variable. -/
partial def getExistVars : Esmt → Expr → MetaM (Expr × List EConst × Esmt) :=
  λ x e => getExistVarsAux [] x e

/-- Returns `true` if `e` is of the form `∀ (x : α) , P → ...  → False` -/
def isNegation (e : Expr) : MetaM Bool := do
 match ← forallTelescopeReducing e (λ _ x => return x) with
 | .const `False _ => return true
 | _ => return false


def checkNegations : PropEvalM Unit := do
 if ← isNegation <| ← getGroundExpr then
  modify (λ s => {s with negativeFormG := true})
 if ← isNegation <| ← getTestExpr then
  modify (λ s => {s with negativeFormT := true})
 return ()

 /-
    Recall that all well-formed formulae (in system E) are of the form
        `∀ x1 .. xn , P → ∃ y1 .. yn ...  → Q`
    where P and Q are propositional formulae over the theory in E.

    We refer to `P` as the left-hand-side (LHS) and `Q` as the right-hand-side (RHS)

-/

def splitAndCollectBvarsCore : PropEvalM BvarDelta := do
  /-
  The first step of equivalence checking is to  split the ground-truth and test formulae
  into their respective LHS and RHS, collecting  and instantiating their bound variables.

  To do this properly, we need to check whether either of the propositions is
  asserting a negation, i.e., it is of the form `∀ x1 .. xn , P → Q → False`

  We also record the translation context(s) obtained by turning those bound variables
  of each formulae into free variables, since this will be needed later. -/
  let ⟨lhsG, rhsG, ctxG⟩ ← splitExpr (← groundNegative?) <| ← getGroundExpr
  let ⟨lhsT, rhsT, ctxT⟩ ← splitExpr ( ← testNegative?)  <| ← getTestExpr
  /- Now, extract the existintially quantified variables, and add them to the same
     SMT translation context  -/
  let ⟨rhsG, existVarsG, ctxG'⟩ ← getExistVars ctxG rhsG
  let ⟨rhsT, existVarsT, ctxT'⟩ ← getExistVars ctxT rhsT
  /- Populate all bound variables for each formula -/
  let groundBvars := .setBvars ctxG.consts.toList existVarsG
  let testBvars   := .setBvars ctxT.consts.toList existVarsT

  /- Set each formula's associated translation context -/
  setGroundCtx ctxG'
  setTestCtx ctxT'

  /-
     Update the evaluation context.
     If the formulae are implication-free, add a trivial LHS to ``simulate'' an implication.
     This is just to simplify the logic of the approximate equivalence checker.
  -/
  if !(← inferType lhsG).isProp then
    setGroundLHS q(True)
  else setGroundLHS lhsG
  if !(← inferType lhsT).isProp then
    setTestLHS q(True)
  else setTestLHS lhsT
  setGroundRHS rhsG
  setTestRHS rhsT
  setGroundBvars groundBvars
  setTestBvars testBvars
  return computeDelta groundBvars testBvars


def splitAndCollectBvars : PropEvalM BvarDelta := do
  checkNegations
  return ← splitAndCollectBvarsCore
