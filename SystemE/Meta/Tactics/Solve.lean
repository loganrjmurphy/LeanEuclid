import SystemE.Meta.Tactics.Util
import SystemE.Meta.Smt.Solver

set_option autoImplicit false

open Lean Elab Tactic Meta SystemE.Smt


namespace SystemE.Tactics

open Translation

/- Data Structure for containing various information
   for the `euclid_apply` tactic
   Basically, everything here is used for reconstructing the tactic after
   the solvers have been invoked.


   `rule` : the argument to `euclid_apply, i.e., the application of some axiom to some arguments.
    When elaborated, `rule` will be a term of type `P -> Q`, where `P` is the hole to be filled
    `hole` : The antecedent of the above implication
    `nm ` : The name we will give to the premise `hole` once it is filled
    `isConstr` : True if the instance of `euclid_apply` is "constructive", i.e. is of the form `euclid_apply rule as i`
    `ident` : The identifier to be used to construct the object if `isConstr` is true
    `smtContext` the SMT context generated from the proof state in which `euclid_apply` is invoked
-/
structure EuclidStep where
  rule : Term
  hole : Expr
  holeName : Name
  isConstr := false
  idents : Array Ident
  smtContext : Esmt := default

abbrev EuclidStepM := ReaderT EuclidStep TacticM

namespace EuclidStep

def init (g : MVarId) (hole : Expr) (rule : Term) (idents : Array Ident) : TacticM EuclidStep :=
  g.withContext do
    let n ← getUnusedUserName `aux
    return {hole := hole, holeName := n, rule := rule, isConstr := ¬ idents.isEmpty, idents := idents}

/- Add a new goal whose target is the whole to be filled.
   The original proof state will now have the hole as a premise.
 -/
def pushHole : EuclidStepM Unit := do
  let Γ ← read
  let p ← mkFreshExprMVar Γ.hole MetavarKind.natural
  let (_, mvarIdNew) ← Lean.MVarId.intro1P $ ← (← getMainGoal).assert Γ.holeName Γ.hole p
  replaceMainGoal [p.mvarId!, mvarIdNew]

/- We are now in a proof state where the hole has been filled, so we can reconstruct the tactic and apply the rule -/
private def applyHole (stx : Term) (hnm : Name) : EuclidStepM Unit := do
  let Γ ← read
  if Γ.isConstr then
    evalTactic $ ← `(tactic| obtain ⟨$Γ.idents,*, ($(mkIdent hnm))⟩ := $Γ.rule $stx)
  else
    evalTactic $ ← `(tactic| obtain ($(mkIdent hnm)) := $Γ.rule $stx)

/- invoke `applyHole` only if the hole actually exists -/
def finish : EuclidStepM Unit := do
  let Γ ← read
  withMainContext do
    match (← getLCtx).findFromUserName? Γ.holeName with
    | none =>   dbg_trace "finish: fail" ; failure
    | some d =>
      applyHole (← d.toExpr.toSyntax) (← getUnusedUserName `h) |>.run Γ
      evalTactic $ ← `(tactic| try (clear ($(mkIdent Γ.holeName))))
      evalTactic $ ← `(tactic| try aesop)

end EuclidStep

open EuclidStep

/-
  Solve the given subgoal (a conjunct of `Γ.hole`) using the SMT solvers.
  We call z3 first, then cvc5 if z3 fails, but this can be changed.
  Ideally, we would parallelize.

  If the goal is not proved, we return its type (for printing to the user)
-/
private def solveWithProvers (query : Esmt) (g : MVarId) : TacticM (Option Expr) := do
  let goal ← instantiateMVars (← g.getType)
  -- logInfo m!"{goal}"
  let smtQuery ← addGoal query goal
  match ← evalSmt smtQuery with
  | .unsat =>
    closeWithAxiom g
    return none
  | .sat =>
    logWarning m!"Prover returned SAT"
    failure
  | _ =>
      emitGoalAndCloseWithSorry g
      return goal

private def simpAndSplit : TacticM Syntax :=
  `(tactic| try simp_all ; try split_ands)

/--
The `euclid_finish` tactic tries to prove the current goal using various proof automation, including SMT offloading.
-/

def refersToCong (e : Expr) : MetaM Bool := do
match e.getAppFnArgs with
| (`Triangle.congruent, _) => return true
| _ => return false

def preprocess : TacticM Unit := do
  let ctx ← getLCtx
  for decl in ctx do
    if ← refersToCong decl.type then do
      let hname := decl.userName
      evalTactic $ ← `(tactic| try unfold Triangle.congruent at $(mkIdent hname):ident)
      evalTactic $ ← `(tactic| try simp at $(mkIdent hname):ident)

def EuclidFinish (isApply : Bool) : TacticM Unit := do
  if !isApply then preprocess
  withMainContext do
    let subGoals ← evalTacticAt (← simpAndSplit) (← getMainGoal)
    replaceMainGoal subGoals
    if subGoals.isEmpty then
      return ()
    let ctx ← getESMTfromContext
    let mut unsolved : List Format := []
    for g in subGoals do
      if let some e ← solveWithProvers ctx g then
        unsolved := (← pretty e)::unsolved
    if ¬unsolved.isEmpty then
      traceUnsolved unsolved

syntax "euclid_finish" : tactic

elab "euclid_finish" : tactic => withMainContext <| EuclidFinish false

/-
  Invoked when `euclid_apply` has a hole to be filled.
  `hole` : The expression corresponding to the `Prop` to be filled
  `rule` : The whole argument of `euclid_apply`, e.g. `circle_from_points a b`
  `ident` : The identifier to be used if the `euclid_apply` instance is constructive
-/
private def EuclidSolve : EuclidStepM Unit := do
  pushHole
  EuclidFinish true
  finish

/-
  Main function for `euclid_apply`
-/
def EuclidApply (rule : Term) (idents : Array Ident)  : TacticM Unit := do
  if (← getGoals).length != 1 then
    throwError "euclid_apply only works when there is a single goal"
  let hnm ← getUnusedUserName `h
  let τ ← inferType (← elabTerm rule none) >>= instantiateMVars

  match τ with
  | .forallE _ hole P _ => -- τ is an arrow
    if P.hasLooseBVars then  --  τ is an ∀
      evalTactic $ ← `(tactic| obtain ($(mkIdent hnm)) := $rule)
    else  -- τ is an implication, rather than ∀
      let Γ ← init (← getMainGoal) hole rule idents
      EuclidSolve |>.run Γ
  -- If there is no implication in the rule, i.e. no antecedent/hole to be filled, then just do the construction.
  | e =>
    match e.getAppFnArgs with
    | (``Exists, _) =>  -- τ is `∃ x, ...`
      evalTactic $ ← `(tactic| obtain ⟨$idents,*, ($(mkIdent hnm))⟩ := $rule)
    | _ =>
      evalTactic $ ← `(tactic| obtain ⟨$(mkIdent hnm)⟩ := $rule)

  elimAllConjunctions

syntax "euclid_apply" term : tactic

syntax "euclid_apply" term "as" ident : tactic

syntax "euclid_apply" term "as" "(" ident,+ ")" : tactic

syntax "euclid_assert" term : tactic

elab_rules : tactic
  | `(tactic| euclid_apply $t as $i) =>
    withMainContext $ EuclidApply t #[i]
  | `(tactic| euclid_apply $t as ($is,*)) =>
    withMainContext $ EuclidApply t is
  | `(tactic| euclid_apply $t) =>
    withMainContext $ EuclidApply t #[]

macro_rules
  | `(tactic| euclid_assert $t) => `(tactic| have : $t := by euclid_finish)

set_option systemE.trace false
set_option systemE.solverTime 300

end SystemE.Tactics
