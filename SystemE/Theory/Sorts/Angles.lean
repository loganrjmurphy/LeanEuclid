import SystemE.Theory.Sorts.Primitives
import Mathlib.Data.Real.Basic

/--
An angle ∠ABC is defined by three points.
-/
inductive Angle
| ofPoints (A B C : Point)

namespace Angle

opaque Right : ℝ

opaque degree : Angle → ℝ

instance : Coe Angle ℝ := ⟨degree⟩

end Angle

notation "∟" => Angle.Right

notation:71 "∠" a ":" b ":" c:72 => Angle.degree (Angle.ofPoints a b c)


open Lean PrettyPrinter

@[app_unexpander Angle.degree]
def unexpand_degree : Unexpander
| `($_ (`Angle.ofPoints $a:ident $b:ident $c:ident)) => `(∠ $a:ident : $b:ident : $c:ident)
| _ => throw ()
