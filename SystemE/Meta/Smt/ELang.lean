
/- Symbolic encoding of the System E language in Lean.
   Essentially, this is our intermediate representation between Lean and the SMT encoding. -/

namespace SystemE.Smt

inductive ESort
| Point
| Line
| Segment
| Circle
| Angle
| Area
deriving Inhabited

inductive ERelation
| OnL (point line : String)
| OnC (point circle : String)
| Centre (point circle : String)
| InC (point circle : String)
| SameSide (p₁ p₂ line : String)
| Between (p₁ p₂ p₃ : String)
| IntersectsLL (l₁ l₂ : String)
| IntersectsLC (l c : String)
| IntersectsCC (c₁ c₂ : String)
deriving BEq, Hashable

inductive EFun
| SegLen (endA endB : String)
| Deg (angle : String)


namespace ESort

def toString : ESort → String
| Point => "Point"
| Line => "Line"
| Segment => "Segment"
| Circle => "Circle"
| Angle => "Angle"
| Area => "Area"

instance : ToString ESort := ⟨toString⟩

def asConstDecl : String × ESort → String
| ⟨x, s⟩ => s!"(declare-const {x} {s})"

instance : ToString (String × ESort) := ⟨asConstDecl⟩

end ESort

namespace ERelation

def toString : ERelation → String
| OnL p l => s!"(OnL {p} {l})"
| OnC p C => s!"(OnC {p} {C})"
| Centre p C => s!"(Centre {p} {C})"
| InC p C => s!"(Inside {p} {C})"
| SameSide p₁ p₂ l => s!"(SameSide {p₁} {p₂} {l})"
| Between  p₁ p₂ p₃ => s!"(Between {p₁} {p₂} {p₃})"
| IntersectsLL l₁ l₂ => s!"(IntersectsLL {l₁} {l₂})"
| IntersectsLC l c => s!"(IntersectsLC {l} {c})"
| IntersectsCC c₁ c₂ => s!"(IntersectsCC {c₁} {c₂})"


instance : ToString ERelation := ⟨toString⟩

def asAssertion : ERelation → String := fun r => s!"(assert {r})"

end ERelation

abbrev EConst := String × ESort

inductive EAssertion
| top
| erel (r : ERelation)
| eq (a b : String)
| lt (a b : String)
| lte (a b : String)
| gt (a b : String)
| gte (a b : String)
| neg (x : EAssertion)
| ex (x τ : String) (p : EAssertion)
| all (x τ : String) (p : EAssertion)
| or (a b : EAssertion)
| and (a b : EAssertion)
| imp (a b : EAssertion)
  deriving BEq, Hashable

namespace EAssertion

instance : Inhabited EAssertion := ⟨EAssertion.eq "false" "true"⟩

def toString : EAssertion → String
| .top => "true"
| .erel r => s!"{r}"
| .and a b => s!"(and {toString a} {toString b})"
| .eq a b => s!"(= {a} {b})"
| .lt a b => s!"(< {a} {b})"
| .lte a b => s!"(<= {a} {b})"
| .gt a b => s!"(> {a} {b})"
| .gte a b => s!"(>= {a} {b})"
| .imp a b => s!"(=> {toString a} {toString b})"
| .neg x => s!"(not {toString x})"
| .ex x τ p => s!"(exists (({x} {τ})) {toString p})"
| .all x τ p => s!"(forall (({x} {τ})) {toString p})"
| .or a b => s!"(or {toString a} {toString b})"

instance : ToString EAssertion := ⟨toString⟩

def splitConjuncts : EAssertion → List EAssertion
| .and a b => splitConjuncts a ++ splitConjuncts b
| x => [x]

end EAssertion

end SystemE.Smt
