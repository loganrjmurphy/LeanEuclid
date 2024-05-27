set_option autoImplicit false

inductive EvalMode
| justBvars
| skipApprox
| onlyApprox
| full

structure EvalConfig where
  instanceName : String := "my_eval_inst"
  nPermutations : Nat := 10
  equivSolverTime : Nat := 120
  approxSolverTime : Nat := 5
  mode : EvalMode := .justBvars
  writeResult : Bool := false
  outputFile : String  := "E3/out/result.json"

instance : Inhabited EvalConfig := ⟨{}⟩
