set_option autoImplicit false

inductive EvalMode
| justBvars
| skipApprox
| onlyApprox
| full


def E3.default_out_dir : String := "E3/_out/result.json"

structure EvalConfig where
  instanceName : String := "my_eval_inst"
  nPermutations : Nat := 3
  equivSolverTime : Nat := 120
  approxSolverTime : Nat := 5
  mode : EvalMode := .justBvars
  writeResult : Bool := false
  outputFile : String  := E3.default_out_dir

instance : Inhabited EvalConfig := ⟨{}⟩
