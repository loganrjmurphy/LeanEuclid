import Lean
import SystemE
import E3.Util.String
open Lean Meta SystemE.Smt
set_option autoImplicit false

/- Data Structure for Storing Names of bound variables-/
structure BoundVars where
  uPoints : List String
  uLines : List String
  uCircles : List String
  ePoints : List String
  eLines : List String
  eCircles : List String
  deriving DecidableEq

instance : Inhabited BoundVars := ⟨⟨[],[],[],[],[],[]⟩⟩

namespace BoundVars

def empty : BoundVars := default

inductive Kind
| univ
| exist

def addExprAsObject : BoundVars  → Kind → String → Expr → BoundVars
| names, k, nm, type =>
  match k,type with
  | .univ, (Expr.const `Point []) => {names with uPoints := nm::names.uPoints}
  | .univ, (Expr.const `Line []) =>  {names with uLines := nm::names.uLines}
  | .univ, (Expr.const `Circle []) =>  {names with uCircles := nm::names.uCircles}
  | .exist, (Expr.const `Point []) => {names with ePoints := nm::names.ePoints}
  | .exist, (Expr.const `Line []) =>  {names with eLines := nm::names.eLines}
  | .exist, (Expr.const `Circle []) =>  {names with eCircles := nm::names.eCircles}
  | _,_ => names

def addFromList : BoundVars → Kind → List EConst → BoundVars
| names, _, [] => names
| names, k, ⟨nm,typ⟩::xs =>
    match k, typ with
    | .univ, .Point => addFromList {names with uPoints := nm::names.uPoints} .univ  xs
    | .univ, .Line => addFromList {names with uLines := nm::names.uLines} .univ xs
    | .univ, .Circle => addFromList {names with uCircles := nm::names.uCircles} .univ xs
    | .exist, .Point => addFromList {names with ePoints := nm::names.ePoints} .exist  xs
    | .exist, .Line => addFromList {names with eLines := nm::names.eLines} .exist xs
    | .exist, .Circle => addFromList {names with eCircles := nm::names.eLines} .exist xs
    | _, _ => names


def setBvars (u e : List EConst) : BoundVars :=
 addFromList (addFromList empty .univ u) .exist e


def univBvarsFromList (xs : List EConst) : BoundVars := addFromList empty .univ xs

def existBvarsFromList (xs : List EConst) : BoundVars := addFromList empty .exist xs


def map (f : String → String) : BoundVars → BoundVars
| ⟨ ups, uls, ucs, eps, els, ecs⟩ =>
  ⟨ f <$> ups, f <$> uls, f <$> ucs, f <$> eps, f <$> els, f <$> ecs⟩

end BoundVars


def forJson : BoundVars → String
| ⟨ ups, uls, ucs, eps, els, ecs⟩ =>
  let upoints_quoted := ups.map quoted
  let ulines_quoted := uls.map quoted
  let ucircles_quoted := ucs.map quoted
  let epoints_quoted :=  eps.map quoted
  let elines_quoted := els.map quoted
  let ecircles_quoted := ecs.map quoted
  let uvars := s!"\"points\" : {upoints_quoted}, \"lines\" : {ulines_quoted}, \"circles\" : {ucircles_quoted}"
  let evars := s!"\"points\" : {epoints_quoted}, \"lines\" : {elines_quoted}, \"circles\" : {ecircles_quoted}"
  s!"\"univ\" : \{{uvars}}, \n\"exist\" : \{{evars}}"



structure BvarDelta where
  uPoint : Int
  uLine : Int
  uCircle : Int
  ePoint : Int
  eLine : Int
  eCircle : Int

namespace BvarDelta

instance : Inhabited BvarDelta := { default := .mk 0 0 0 0 0 0}

def isMatch : BvarDelta → Bool
| ⟨up,ul,uc,ep,el,ec⟩ => up == 0 && ul == 0 && uc == 0 && ep == 0 && el == 0 && ec == 0


def toJson : BvarDelta → String
| ⟨up,ul,uc,ep,el,ec⟩ =>
  wrapObject s!"\"uPoints\": {up}, \"uLines\": {ul},\"uCircles\": {uc}, \"ePoints\": {ep},\"eLines\": {el}, \"eCircles\": {ec}"

instance : ToString BvarDelta := ⟨toJson⟩

end BvarDelta

def computeDelta : BoundVars → BoundVars → BvarDelta
| ⟨up, ul, uc, ep, el, ec⟩, ⟨ up', ul', uc', ep', el', ec'⟩ =>
  {
    uPoint := (up'.length : Int)  - (up.length : Int)
    uLine := (ul'.length : Int)  - (ul.length : Int)
    uCircle :=  (uc'.length : Int)  - (uc.length : Int)
    ePoint :=  (ep'.length : Int)  - (ep.length : Int)
    eLine :=  (el'.length : Int)  - (el.length : Int)
    eCircle :=  (ec'.length : Int)  - (ec.length : Int)
  }
