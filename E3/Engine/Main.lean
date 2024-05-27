import E3.Engine.EquivCheck
import E3.Engine.Wf

open Lean

set_option autoImplicit false

def runStdEquiv (cfg : EvalConfig) (ctx : EvalCtx)  (old : E3Result) : MetaM E3Result := do
  let ⟨eq,ctx'⟩ ← checkFullIff.run ctx
  let tmp := old.addEquivResult eq
  if cfg.writeResult = false then
    IO.println s!"[E3] {eq}"
  if ← getTestUnsat.run' ctx' then
    IO.println "[E3] warning: test proposition is unsatisfiable"
  return tmp.addTestUnsatResult (← getTestUnsat.run' ctx')

def runApproxEquiv (r : E3Result) (cfg : EvalConfig) (ctx : EvalCtx) : MetaM Unit := do
    if !r.bvarDelta.isMatch then throwError "[E3] error: cannot run approximate equivalence checking due to mismatched bvars" ; return ()
    else
      let ⟨res,_⟩ ← approxChecker.run ctx
      let result := r.addApproxResult res
      writeResult cfg.instanceName cfg.outputFile result

def E3Main (init : EvalCtx) : MetaM Unit := do
  let ⟨bvars,ctx⟩ ← splitAndCollectBvars.run init
  let mut result : E3Result :=  {bvarDelta := bvars}
  let cfg := ctx.config
  match cfg.mode with
  | .justBvars =>
    logInfo m!"{result}"
    writeResult cfg.instanceName cfg.outputFile result
  | .onlyApprox => runApproxEquiv result cfg ctx
  | .skipApprox =>
    result ← runStdEquiv cfg ctx result
    logInfo m!"{result}"
    writeResult cfg.instanceName cfg.outputFile result
  | .full =>
    result ← runStdEquiv cfg ctx result
    if result.equivSuccess then
      logInfo "[E3] info: match found, skipping approximate equivalence checking"
      writeResult cfg.instanceName cfg.outputFile result
      logInfo m!"{result}"
    else
      runApproxEquiv result cfg ctx


def parseArgs (args : List String) : IO (Option EvalConfig) := do
  if args.length < 6 then
    IO.println "[E3] error: insufficient number of arguments"
    return none
  else
    let name := args[0]!
    let mode := args[1]!
    let mode_result := match mode with | "bvars" => EvalMode.justBvars | "full" => .full | "skipApprox" => .skipApprox | "onlyApprox" => .onlyApprox | _ => .justBvars
    let nPermutations : Nat := args[2]!.toNat!
    let eqSolverTime := args[3]!.toNat!
    let appSolverTime := args[4]!.toNat!
    let writeResult? := args[5]!
    let writeResult := match writeResult? with | "true" => true | _ => false
    if writeResult then if args.length < 7 then
      IO.println "[E3] error: insufficient number of arguments"
      return none
    let outputJsonFile := if writeResult then args[6]! else "E3/out/result.json"
    let x : EvalConfig := {
        instanceName := name, mode := mode_result, nPermutations := nPermutations, equivSolverTime := eqSolverTime, approxSolverTime := appSolverTime, writeResult := writeResult, outputFile := outputJsonFile}
    return x

def runE3fromIO (ground test : Expr) : Option EvalConfig →  IO Unit
| none => return ()
| some cfg => do
  let ⟨⟨g,t⟩,_⟩ ← Meta.MetaM.toIO (preprocessExpr ground test) E3Ctx (← E3State)
  let y : EvalCtx := {instanceName := cfg.instanceName, groundExpr := g, testExpr := t, config := cfg}
  let _ ← Meta.MetaM.toIO (E3Main y) E3Ctx (← E3State)
  return ()
