import Lean
import E3.Util.String

set_option autoImplicit false

open Lean



structure ImpResult where
  totalConjuncts : Nat
  solvedConjuncts : Nat

namespace ImpResult

def success : ImpResult → Bool
| ⟨a,b⟩ => a==b

def toString : ImpResult → String
| ⟨a,b⟩ => wrapObject s!"\"solved\" : {b}, \"total\" : {a}"

instance : ToString ImpResult := ⟨toString⟩

end ImpResult

def permString (perm : HashMap String String) : Id (List String) :=
  perm.toList.map (λ ⟨key,val⟩ =>  s!"\"{key} ↦ {val}\"")

structure PermutationResult where
  permutation : HashMap String String
  fwdLHS : ImpResult
  bwdLHS : ImpResult
  fwdRHS : ImpResult
  bwdRHS : ImpResult

namespace PermutationResult

def toString : PermutationResult → String
| ⟨perm, fwdL, bwdL, fwdR, bwdR⟩  =>
  wrapObject s!"\"bvar_map\" : {permString perm}, \"fwdLHS\" : {fwdL}, \"bwdLHS\" : {bwdL}, \"fwdRHS\" : {fwdR}, \"bwdRHS\" : {bwdR}"

instance : ToString PermutationResult := ⟨toString⟩

end PermutationResult

structure ApproxResult where
  mapping : HashMap String PermutationResult

namespace ApproxResult

def addResult : ApproxResult → String → HashMap String String → ImpResult → ImpResult → ImpResult → ImpResult → ApproxResult
| .mk m, nm, perm, fwdL, bwdL, fwdR, bwdR => .mk <| m.insert nm <| .mk perm fwdL bwdL fwdR bwdR

def toJson : ApproxResult → String
| .mk mapping =>
  let mapJson := mapping.toList.map (λ ⟨key,val⟩ => wrapObject s!"\"{key}\" : {val}")
  s!"{mapJson}"


end ApproxResult
