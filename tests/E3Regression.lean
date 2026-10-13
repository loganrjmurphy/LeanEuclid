import E3
import Qq

open Lean Qq SystemE.Smt

def checkProofCaches : MetaM Unit := do
  let (_, ctx) ← (do
    addProofLHS .top false
    addProofRHS .top true).run { instanceName := "cache-regression" }
  unless ctx.learnedLHS[EAssertion.top]? == some false do
    throwError "RHS cache update overwrote the LHS cache"
  unless ctx.learnedRHS[EAssertion.top]? == some true do
    throwError "RHS cache update was lost"

def main (args : List String) : IO Unit := do
  let _ ← Meta.MetaM.toIO checkProofCaches E3Ctx (← E3State)
  let output := args[0]!
  let expression : Expr := q(∀ (a b : Point), a ≠ b → b ≠ a)
  for mode in [EvalMode.justBvars, EvalMode.skipApprox] do
    runE3fromIO expression expression (some {
      instanceName := "no-write", mode := mode,
      writeResult := false, outputFile := output })
    if ← (System.FilePath.mk output).pathExists then
      throw (IO.userError "writeResult=false unexpectedly created an output file")
  runE3fromIO expression expression (some {
    instanceName := "write", mode := .justBvars,
    writeResult := true, outputFile := output })
  unless ← (System.FilePath.mk output).pathExists do
    throw (IO.userError "writeResult=true did not create the nested output path")
