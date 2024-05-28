import Lean
import E3.Data
import E3.Util.String
import SystemE.Tactics

open Lean Elab Command

set_option autoImplicit false

def writeResult (name fileName : String) (x : E3Result) : IO Unit :=
  IO.FS.writeFile (fileName) (x.toJson (name))


/- Environment, State, and Context for initializing equivalence checker -/
def E3Env : IO Environment := importModules #[`SystemE] {}
def E3Ctx : Core.Context := {fileName := "<empty>",fileMap := .ofString ""}
def E3State : IO Core.State := return {env := ← E3Env}

-- Temporarily files for Lean/Python communication,
def permInFile (name : String) :=  s!"E3/_tmp/{name}_in.json"
def permOutFile (name : String) := s!"E3/_tmp/{name}_out.json"

/-
The following functions are used for interacting with `choosePerms.py`,
which chooses unifications of bound variables between ground truth and test propositions
--/

def permChooser (inFile outFile : String) (nPerms : Nat) :=  IO.Process.spawn  {
      cmd := "python3",
      args := #["E3/Engine/choosePerms.py","--inFile", inFile, "--outFile", outFile, "--N", s!"{nPerms}"],
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }


def readPermOutput (file: String) : IO (Except String ((List String) × (List (List String)))) := do
  let jsonString ← IO.FS.readFile file
  match (Json.parse jsonString) >>= (Json.getObjVal? . "ground") >>= Json.getArr? with
    | .error _ => .error "[E3/choosePerms] error: ground prop. not found"
    | .ok g => match g.mapM Json.getStr? with
      | .error _ => .error "[E3/choosePerms] error: ground list not wf"
      | .ok gs => match (Json.parse jsonString) >>= (Json.getObjVal? . "perms") >>= Json.getArr? with
        | .error _ =>  .error "[E3/choosePerms] error: perms not found"
        | .ok arr => match arr.mapM Json.getArr? with
          | .error _ => .error "[E3/choosePerms] error: test prop. names not well-formed"
          | .ok ls => match ls.toList.mapM (λ xs => xs.mapM Json.getStr?) with
            | .error _ => .error "[E3/choosePerms] error: test prop. names not well-formed"
            | .ok xs => return .ok ⟨gs.toList, xs.map (Array.toList) ⟩

def permutationHeuristic (inFile outFile raw guarded tjson gjson : String) (nperms : Nat) :  IO (Except String (List String × List (List String))) := do
  let fileContents := formatPermutationJson raw guarded tjson gjson
  IO.FS.writeFile inFile fileContents
  let process ← permChooser inFile outFile nperms
  process.stdin.flush
  let (_, process) ← process.takeStdin
  let _ ← process.wait
  let err := (← process.stderr.readToEnd).trim
  if err != "" then
      .error err
  else
    readPermOutput outFile

def E3.clean_tmp_dir (name : String)  : IO Unit := do
    IO.FS.removeFile (permInFile name)
    IO.FS.removeFile (permOutFile name)
