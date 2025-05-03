import SystemE.Meta.Smt.ELang
import SystemE.Theory.Relations
import SystemE.Theory.Sorts
import Lean
import Std.Data.HashMap

set_option autoImplicit false

open Lean Elab Tactic Meta Std

namespace SystemE.Smt

/- Data structure for storing the declarations extracted from proof context -/
/-
 `consts` : A list of pairs <name, T> : `String` × `ESort` corresponding to geomtetric object variables
 `fetchIdName` : a mapping of free variables to their sanitized name in `consts`.
 `asserts` : A list of `EAssertions`, i.e. propositions in System E
 `numId` : The number of fresh (sanitized) variables which have been created so far
            The `k`'th fresh variable created will have name `fresh_{k-1}`
-/
structure Esmt where
  consts : Array EConst
  fetchIdName : HashMap FVarId String := {}
  asserts : Array EAssertion
  numId : ℕ := 0
deriving Inhabited

abbrev EsmtM := StateT Esmt MetaM

instance : MonadLiftT EsmtM MetaM := {
  monadLift := λ x =>  x.run' {consts := #[], asserts := #[]}
}

namespace Esmt

def addConstDecl (x : EConst) : EsmtM Unit :=
  modify fun Γ => {Γ with consts := Γ.consts.push x}

def addAssertion (x : EAssertion) : EsmtM Unit :=
  modify fun Γ => {Γ with asserts := Γ.asserts.push x}

def addVar (x : FVarId) (y : String) : EsmtM Unit :=
  modify fun Γ => {Γ with fetchIdName := Γ.fetchIdName.insert x y, numId := Γ.numId + 1}

def getSanitizedName! (fvarId : FVarId) : EsmtM String := do
  return (← get).fetchIdName.get! fvarId

/- Translate an Esmt to a List of Strings, formatted as SMT-Lib2 commands
   This is only really used for tracing/debugging.
-/
private def toArrayString : Esmt → Array String
  | ⟨consts, _, asserts,_⟩ =>
    (consts.map ESort.asConstDecl) ++ (asserts.map (λ a => s!"(assert {a})"))

def getVarNum : EsmtM ℕ := do
  return (← get).numId

def incrementVarNum : EsmtM Unit :=
  modify fun Γ => {Γ with numId := Γ.numId + 1}

def toString (e : Esmt) : String :=
  (toArrayString e).foldl (λ s t => s ++ "\n" ++ t) ""

instance : ToString Esmt := ⟨toString⟩

/- Sanitize a variable name for SMT-Lib2 if it is not purely alphanumeric
   In practice, this is to accomodate things like `a'` or `xₒ`
-/
def sanitize (s : String) : EsmtM String := do
  if s.any (fun e => !(e.isAlphanum || e == '_')) then
    return "v" ++ s!"_{(← get).numId}"
  else
    return s

def replaceNames : Esmt → HashMap FVarId String → Esmt
| .mk consts _ asserts n, new => .mk consts new asserts n

end Esmt

open Esmt

def getSort? : Expr → Option ESort
| (Expr.const `Point []) => some ESort.Point
| (Expr.const `Line []) => some ESort.Line
| (Expr.const `Circle []) => some ESort.Circle
| _ => none

def getSort! : Expr → ESort
| (Expr.const `Point []) => ESort.Point
| (Expr.const `Line []) => ESort.Line
| (Expr.const `Circle []) => ESort.Circle
| (Expr.const `Area []) => ESort.Area
| _ => unreachable!


def getSanitizedName! (fvarId : FVarId) : EsmtM String := do
  match (← get).fetchIdName.get? fvarId with
  | none => throwError "[SystemE.Smt] translation error : variable not found"
  | some v => return v


end SystemE.Smt
