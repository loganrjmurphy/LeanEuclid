
structure EquivResult where
  groundImpTest : Bool
  testImpGround : Bool

namespace EquivResult

def isEquiv : EquivResult → Bool
| ⟨true, true⟩ => true
| _ => false

def toString : EquivResult → String
| ⟨true, true⟩ => "propositions are equivalent"
| ⟨true, false⟩ => "prediction is strictly weaker than ground truth"
| ⟨false, true⟩ => "prediction is strictly stronger than ground truth"
| _ => "no conclusion made between prediction and ground truth"

def toJson : EquivResult → String
| ⟨true, true⟩ => "\"equiv\""
| ⟨true, false⟩ => "\"ground_imp_test\""
| ⟨false, true⟩ => "\"test_imp_ground\""
| _ => "\"no_conclusion\""

instance : ToString EquivResult := ⟨EquivResult.toString ⟩

end EquivResult
