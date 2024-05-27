import SystemE.Theory.Sorts.Segments

/--
Triangles are called "Areas" in [Avigad et al., 2009]
-/
inductive Triangle
| ofPoints (a b c : Point)

namespace Triangle

opaque area : Triangle → ℝ

notation:max "△" a ":" b ":" c:66 => ofPoints a b c

noncomputable instance : Coe Triangle Real := ⟨area⟩

instance : LT Triangle := ⟨fun a b => area a < area b⟩

end Triangle
