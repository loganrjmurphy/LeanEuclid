
structure EquivResult where
  groundImpTest : Bool
  testImpGround : Bool

namespace EquivResult

def isEquiv : EquivResult → Bool
| ⟨true, true⟩ => true
| _ => false

def toString : EquivResult → String
| ⟨true, true⟩ => "Props match"
| ⟨true, false⟩ => "Test prop. is strictly weaker than ground prop."
| ⟨false, true⟩ => "Test prop. is strictly stronger than ground prop."
| _ => "no conclusion."

def toJson : EquivResult → String
| ⟨true, true⟩ => "\"equiv\""
| ⟨true, false⟩ => "\"ground_imp_test\""
| ⟨false, true⟩ => "\"test_imp_ground\""
| _ => "\"no_conclusion\""

instance : ToString EquivResult := ⟨EquivResult.toString ⟩

end EquivResult
