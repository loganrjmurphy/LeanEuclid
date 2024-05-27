import E3.Data.BoundVars
import E3.Data.EquivResult
import E3.Data.ApproxResult

structure E3Result where
  bvarDelta : BvarDelta
  equiv : Option EquivResult := none
  approx : Option ApproxResult := none
  testUnsat : Bool := false


namespace E3Result

def equivSuccess : E3Result → Bool
| .mk _ (some r) _ _ => r.isEquiv
| _ => false

def addEquivResult : E3Result → EquivResult → E3Result :=
  λ x r => {x with equiv := r}

def addApproxResult : E3Result → ApproxResult → E3Result :=
  λ x r => {x with approx := r}

def addTestUnsatResult : E3Result → Bool → E3Result :=
  λ x b => {x with testUnsat := b}

def toJson (name : String) : E3Result → String
| .mk bvars bin approx b =>
  let bin_str := match bin with | none => "\"none\"" | some r => r.toJson
  let approx_str := match approx with | none => "\"none\"" | some r => r.toJson
  let contents := wrapObject s!"\"bvars\" : {bvars.toJson}, \n \"binary_check\" : {bin_str}, \n \"approx_check\" : {approx_str}, \n\"testUnsat\" : \"{b}\""
  wrapObject s!"\"{name}\" : \n {contents}"

instance : ToString E3Result := ⟨toJson "E3-result"⟩


end E3Result
