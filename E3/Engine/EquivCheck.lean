import E3.Util.IO
import E3.Engine.Preprocess
import E3.Data.EvalCtx
import SystemE.Smt

open Qq
set_option autoImplicit false

open Lean Elab Command Tactic Meta Smt.Solver SystemE.Smt SystemE.Tactics

/-- Modified version of `evalSmt`used by E3. Similar to the normal usage in `euclid_*` tactics, except we include different background theoeries depending on the context -/
def evalSmt' (unsatCheck : Bool) (Γ : Option Esmt) (t : Nat) (x : EAssertion) : PropEvalM Bool := do
  let background :=
    -- if we are just checking to see whether `Test` is unsatisfiable
    if unsatCheck then euclidTheory ++ euclidConstructionRulesFull
    else match Γ with
      -- if we are checking equivalence at teh formula-level
      | none => euclidTheory ++ euclidConstructionRulesShort
      -- if we are checking individual clauses
      | some ctx => euclidTheory ++ SystemE.Tactics.Translation.fromEsmt ctx
  let assertion :=  s!"{x}" |> Smt.Term.literalT |> Smt.Command.assert
  let query := addCommands (background ++ [assertion]) *> checkSat
  let solverState ← Smt.Solver.create t
  let result ← (StateT.run' query solverState : MetaM _)
  match result with | .unsat => return true | _ => return false


/- Check `Ground <==> Test`
   Also try to check whether `Test` is actually unsatisfiable
-/
def checkFullIff : PropEvalM EquivResult := do
  let groundProp ← translateGroundExpr
  let testProp ← translateTestExpr
  let fwd : EAssertion := .neg <| .imp groundProp testProp
  let bwd : EAssertion := .neg <| .imp testProp groundProp
  let fwdResult ← evalSmt' false none (←getEvalConfig).equivSolverTime fwd
  let bwdResult ← evalSmt' false none (←getEvalConfig).equivSolverTime bwd
  /- TODO (Logan): Make unsat check time a configuration option-/
  if ← evalSmt' true none 10 testProp then
    logInfo "test assertion is unsatisfiable"
    modify (λ s => {s with testUnsat := true})
  return { groundImpTest := fwdResult, testImpGround := bwdResult}

/--
  Check `Test ⟹ GroundTruth` in the approximate checker.
  This function is used for both the LHS (comparing preconditions) and RHS (comparing postconditions)
-/
def solveBwd (test ground : EAssertion) (ctx : Esmt) (assumptions : List EAssertion) : PropEvalM ImpResult := do
  let assumptions := assumptions ++ test.splitConjuncts
  let obligations := ground.splitConjuncts
  let total := obligations.length
  let ctx' : Esmt := {ctx with asserts := assumptions.toArray}
  let mut solved : Nat := 0
  for goal in obligations do
    if ← evalSmt' false ctx' (← getEvalConfig).approxSolverTime (.neg goal) then
      solved := solved + 1
  return .mk total solved

/--
  Assuming preconditions of `GroundTruth`, prove preconditions of `Test`.
-/
def solveFwdLHS (ground test : EAssertion) (ctx : Esmt)   : PropEvalM ImpResult := do
  let assumptions := ground.splitConjuncts
  let obligations := test.splitConjuncts
  let ctx' : Esmt := {ctx with asserts := assumptions.toArray}
  let mut solved : Nat := 0
  for goal in obligations do
    if ← seenGoalLHS goal then
      if ← isProvenLHS goal then solved := solved + 1 else continue
    else
      if ← evalSmt' false ctx' (← getEvalConfig).approxSolverTime (.neg goal) then
        addProofLHS goal true
        solved := solved + 1
      else addProofLHS goal false
  return .mk obligations.length solved

/--
  Assuming postconditions of `GroundTruth`, prove postconditions of `Test`.
-/
def solveFwdRHS (ground test : EAssertion) (ctx : Esmt)  (assumptions : List EAssertion) : PropEvalM ImpResult := do
  let assumptions := assumptions ++ ground.splitConjuncts
  let obligations := test.splitConjuncts
  let total := obligations.length
  let ctx' : Esmt := {ctx with asserts := assumptions.toArray}
  let mut solved : Nat := 0
  for goal in obligations do
    if ← seenGoalRHS goal then
      if ← isProvenRHS goal then solved := solved + 1 else continue
    else
      if ← evalSmt' false ctx' (←getEvalConfig).approxSolverTime (.neg goal) then
        addProofRHS goal true
        solved := solved + 1
      else addProofRHS goal false
  return .mk total solved

/-- Check (one half of) `GroundTruth <===> Test` using the approximate checker.
    Note that this function operates on either the preconditions (LHS) or postconditions (RHS)
-/
def checkIffApprox (ground test : EAssertion) (isLHS : Bool) (assumptions : List EAssertion)  : PropEvalM (ImpResult × ImpResult) := do
  -- IO.println "checking fwd direction..."
  let fwd ←
    if isLHS then
      solveFwdLHS ground test (← getGroundCtx)
    else
      solveFwdRHS ground test (← getGroundCtx) assumptions
  -- IO.println "checking bwd direction..."
  let bwd ← solveBwd test ground (← getGroundCtx) assumptions
  return ⟨fwd, bwd⟩

def solvePerms
  (groundNames : List String)
  (perms : List (List String)) : PropEvalM ApproxResult := do
  let init_map ← getTestNameMap
  let mut result : ApproxResult := .mk {}
  let mut i : Nat := 0
  for perm in perms do
    -- IO.println "Checking perm..."
    let subst : HashMap String String := HashMap.ofList <| perm.zip groundNames
    setTestNames <| ← mergeMaps init_map subst
    -- IO.println "checking LHS ..."
    let ⟨fwdLHS, bwdLHS⟩ ← checkIffApprox (← getGroundLHS) (← translateTestLHS) true []
    let mut assumptions : List EAssertion := []
    if fwdLHS.success && bwdLHS.success then
      --  IO.println "LHS proved equivalent; preconditions will be included for RHS"
       assumptions := (← getGroundLHS).splitConjuncts
    -- IO.println "checking RHS ..."
    let ⟨fwdRHS, bwdRHS⟩ ← checkIffApprox (←getGroundRHS) (← translateTestRHS) false assumptions
    result := result.addResult s!"permutation_{i}" subst fwdLHS bwdLHS fwdRHS bwdRHS
    i := i + 1
  return result

/--
  Check `GroundTruth <===> Test` using the approximate equivalence checker.
  We do some preprocessing, then handoff to  `choosePerms.py` to choose the best unifications
  (permutations) of bound variables (using a string similarity heuristic).

  For each proposed unification, we check bidirectional implications in a clause-by-clause manner.
-/
def approxChecker  : PropEvalM ApproxResult := do
  let groundE ← getGroundExpr
  let guardedE := renameBVars (← getTestExpr)
  let gjson := forJson <| ← getGroundBvars
  let tjson := forJson <| .map ("grd_"++ .)  <| ← getTestBvars
  let mut ⟨rawGroundLHSExpr, _, _⟩ ← splitExpr (← groundNegative?) groundE
  if !(← inferType rawGroundLHSExpr).isProp then
    rawGroundLHSExpr := q(True)
  let rawFull : String := Format.pretty (← pretty groundE) (width := 10000)
  let guardedFull : String := Format.pretty (← pretty guardedE) (width := 10000)
  match ← permutationHeuristic (permInFile (←getInstName)) (permOutFile (←getInstName)) rawFull guardedFull tjson gjson (← getEvalConfig).nPermutations with
      | .error _ => return .mk {}
      | .ok ⟨ground, perms⟩ =>
        -- E3.clean_tmp_dir (← getInstName)
        let r ← solvePerms ground perms
        return r
