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
  outputFile : String  := "E3/out/bar.json"

instance : Inhabited EvalConfig := ⟨{}⟩
