import E3.Data.BoundVars
import E3.Data.Config
import UniGeo.Relations

open Lean Elab Tactic Meta SystemE.Smt

set_option autoImplicit false


abbrev LearnedProofs : Type  := HashMap EAssertion Bool

structure EvalCtx where
  config : EvalConfig := default
  instanceName : String
  groundExpr : Expr := default
  testExpr : Expr := default
  groundCtx : Esmt := default
  testCtx : Esmt := default
  groundLHS : EAssertion := default
  groundRHS : EAssertion := default
  testLHS : Expr := default
  testRHS : Expr := default
  groundBvars : BoundVars := default
  testBvars : BoundVars := default
  negativeFormG : Bool := false
  negativeFormT : Bool := false
  testUnsat : Bool := false

  -- When checking the forward direction of an implication (Ground ==> Test),
  -- The clauses of the ground proposition never changes between permutations of bound variables,
  -- only those of the test proposition.
  -- Since only a small number of conjuncts are changed between two given permutations,
  -- we want to avoid re-checking any conjuncts we have already seen.
  -- So we record them here.
  learnedLHS : LearnedProofs := {}
  learnedRHS : LearnedProofs := {}

deriving Inhabited

abbrev PropEvalM := StateT EvalCtx MetaM

/-- Wrapper for SMT translation in PropEval monad -/
def translateExprOrThrowError (ctx : Esmt) (e : Expr) : PropEvalM  EAssertion := do
  match ← translateExpr e |>.run' ctx with
  | .ok r => return r
  | .error msg => throwError msg

/- Getter Functions -/

def getEvalConfig : PropEvalM EvalConfig := do
  get >>= pure ∘ EvalCtx.config

def getTestUnsat : PropEvalM Bool := do
  get >>= pure ∘ EvalCtx.testUnsat

def getInstName : PropEvalM String := do
  get >>= pure ∘ EvalCtx.instanceName

def getGroundExpr : PropEvalM Expr := do
  get >>= pure ∘ EvalCtx.groundExpr

def getTestExpr : PropEvalM Expr := do
  get >>= pure ∘ EvalCtx.testExpr

def getTestLHS : PropEvalM Expr := do
  get >>= pure ∘ EvalCtx.testLHS

def getTestRHS : PropEvalM Expr := do
  get >>= pure ∘ EvalCtx.testRHS

def getTestNameMap : PropEvalM (HashMap FVarId String) := do
  get >>= pure ∘ Esmt.fetchIdName ∘ EvalCtx.testCtx

def getTestCtx : PropEvalM Esmt := do
  get >>= pure ∘ EvalCtx.testCtx

def getGroundLHS : PropEvalM EAssertion := do
  get >>= pure ∘ EvalCtx.groundLHS

def getGroundRHS : PropEvalM EAssertion := do
  get >>= pure ∘ EvalCtx.groundRHS

def getGroundCtx : PropEvalM Esmt := do
  get >>= pure ∘ EvalCtx.groundCtx

def getGroundBvars : PropEvalM BoundVars := do
  get >>= pure ∘ EvalCtx.groundBvars

def getTestBvars : PropEvalM BoundVars := do
  get >>= pure ∘ EvalCtx.testBvars

def groundNegative? : PropEvalM Bool := do
  get >>= pure ∘ EvalCtx.negativeFormG

def testNegative? : PropEvalM Bool := do
  get >>= pure ∘ EvalCtx.negativeFormT

/- Translation Functions -/

def translateGroundExpr : PropEvalM EAssertion := do
  getGroundExpr >>= translateExprOrThrowError {consts :=#[], asserts:=#[]}

def translateTestExpr : PropEvalM EAssertion := do
  getTestExpr >>= translateExprOrThrowError {consts :=#[], asserts:=#[]}

def translateTestLHS : PropEvalM EAssertion := do
  getTestCtx >>= (getTestLHS >>= translateExprOrThrowError .)

def translateTestRHS : PropEvalM EAssertion := do
  getTestCtx >>= (getTestRHS >>= translateExprOrThrowError .)

/- Setter Functions -/

def setConfig (x : EvalConfig) : PropEvalM Unit :=
  modify (λ s => {s with config := x} )

def setTestNames (mapping : HashMap FVarId String) : PropEvalM Unit :=
  modify (λ s => {s with testCtx := {s.testCtx with fetchIdName := mapping}})

def setGroundLHS (e : Expr) : PropEvalM Unit := do
  let lhs ← getGroundCtx >>= (translateExprOrThrowError . e)
  modify (λ s => {s with groundLHS := lhs})

def setTestLHS (e : Expr) : PropEvalM Unit :=
  modify (λ s => {s with testLHS := e})

def setGroundRHS (e : Expr) : PropEvalM Unit := do
  let rhs ← getGroundCtx >>= (translateExprOrThrowError . e)
  modify (λ s => {s with groundRHS := rhs})

def setTestRHS (e : Expr) : PropEvalM Unit :=
  modify (λ s => {s with testRHS := e})

def setGroundCtx (ctx : Esmt) : PropEvalM Unit :=
  modify (λ s => {s with groundCtx := ctx})

def setTestCtx (ctx : Esmt) : PropEvalM Unit :=
  modify (λ s => {s with testCtx := ctx})

def setGroundBvars (bs : BoundVars) : PropEvalM Unit :=
  modify (λ s => {s with groundBvars := bs} )

def setTestBvars (bs : BoundVars) : PropEvalM Unit :=
  modify (λ s => {s with testBvars := bs} )

def addProofLHS (x : EAssertion) (b : Bool) : PropEvalM Unit :=
  modify (λ s => {s with learnedLHS := s.learnedLHS.insert x b})

def addProofRHS (x : EAssertion) (b : Bool) : PropEvalM Unit :=
  modify (λ s => {s with learnedLHS := s.learnedLHS.insert x b})

/- Queries-/

def seenGoalLHS (x : EAssertion) : PropEvalM Bool := do
  get >>= pure ∘ (Lean.HashMap.contains . x) ∘ EvalCtx.learnedLHS

def seenGoalRHS (x : EAssertion) : PropEvalM Bool := do
  get >>= pure ∘ (Lean.HashMap.contains . x) ∘ EvalCtx.learnedRHS

def isProvenLHS (x : EAssertion) : PropEvalM Bool := do
  match (← get).learnedLHS[x] with
  | some b => return b | _ => return false

def isProvenRHS (x : EAssertion) : PropEvalM Bool := do
  match (← get).learnedRHS[x] with
  | some b => return b
  | _ => return false
