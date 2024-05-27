import Lake
open Lake DSL

package «lib» where
  leanOptions := #[⟨`relaxedAutoImplicit, true⟩]

@[default_target]
lean_lib SystemE {
}

lean_lib Book {
}

lean_lib UniGeo {
}

lean_lib E3 {

}

require mathlib from git "https://github.com/leanprover-community/mathlib4"

require smt from git "https://github.com/yangky11/lean-smt.git" @ "main"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

def checkAvailable (cmd : String) : IO Unit := do
  let proc ← IO.Process.output {
    cmd := "which",
    args := #[cmd]
  }
  if proc.exitCode != 0 then
    throw $ IO.userError s!"Cannot find `{cmd}`."

script check do
  checkAvailable "smt-portfolio"
  checkAvailable "z3"
  checkAvailable "cvc5"
  checkAvailable "vampire"
  println! "All requirements are satisfied."
  return 0

script aggregate do
  let bookDir := (← IO.currentDir) / "Book"
  let leanPaths := (← System.FilePath.walkDir bookDir) |>.filter fun p => p.extension = some "lean"
  let sortedPaths := leanPaths.qsort (fun p₁ p₂ => p₁.toString < p₂.toString) |>.toList
  println! sortedPaths
  let code ← sortedPaths.mapM fun p => do
    let lines := (← IO.FS.lines p) |>.filter fun l =>
      ¬(l.startsWith "import" ∨ l.startsWith "namespace" ∨ l.startsWith "end")
    return (String.join $ (lines.map fun l => l ++ "\n").toList).trim ++ "\n\n"
  let codeAll := "import SystemE\n\nnamespace Elements\n\n" ++ String.join code ++ "\nend Elements\n"

  let outFile := bookDir / "All.lean"
  if ← outFile.pathExists then
    IO.FS.removeFile outFile
  IO.FS.writeFile outFile codeAll
  println! codeAll

  return 0
